/*
 * PianoRoll.cpp - implementation of piano roll which is used for actual
 *                  writing of melodies
 *
 * Copyright (c) 2004-2014 Tobias Doerffel <tobydox/at/users.sourceforge.net>
 * Copyright (c) 2008 Andrew Kelley <superjoe30/at/gmail/dot/com>
 *
 * This file is part of LMMS - https://lmms.io
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program (see COPYING); if not, write to the
 * Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
 * Boston, MA 02110-1301 USA.
 *
 */

#include "PianoRoll.h"

#include <QApplication>
#include <QClipboard>
#include <QKeyEvent>
#include <QLabel>
#include <QLayout>
#include <QMargins>
#include <QMdiArea>
#include <QMessageBox>
#include <QPainter>
#include <QPointer>
#include <QScrollBar>
#include <QStyleOption>
#include <QtMath>
#include <QToolButton>

#ifndef __USE_XOPEN
#define __USE_XOPEN
#endif

#include <algorithm> // find, sort, unique, all_of
#include <functional> // greater
#include <memory> // make_unique

#include "AutomationEditor.h"
#include "ActionGroup.h"
#include "BBTrackContainer.h"
#include "Clipboard.h"
#include "ComboBox.h"
#include "ConfigManager.h"
#include "DataFile.h"
#include "debug.h"
#include "DeprecationHelper.h"
#include "DetuningHelper.h"
#include "embed.h"
#include "GuiApplication.h"
#include "gui_templates.h"
#include "InstrumentTrack.h"
#include "MainWindow.h"
#include "Pattern.h"
#include "SongEditor.h"
#include "StepRecorderWidget.h"
#include "TextFloat.h"
#include "TimeLineWidget.h"
#include "FileDialog.h"



typedef AutomationPattern::timeMap timeMap;


// some constants...
const int INITIAL_PIANOROLL_WIDTH = 970;
const int INITIAL_PIANOROLL_HEIGHT = 485;

const int SCROLLBAR_SIZE = 12;
const int PIANO_X = 0;

const int WHITE_KEY_WIDTH = 64;
const int BLACK_KEY_WIDTH = 41;

const int DEFAULT_KEY_LINE_HEIGHT = 12;
const int DEFAULT_CELL_WIDTH = 12;


const int NOTE_EDIT_RESIZE_BAR = 6;
const int NOTE_EDIT_MIN_HEIGHT = 50;
const int KEY_AREA_MIN_HEIGHT = DEFAULT_KEY_LINE_HEIGHT * 10;
const int PR_BOTTOM_MARGIN = SCROLLBAR_SIZE;
const int PR_TOP_MARGIN = 18;
const int PR_RIGHT_MARGIN = SCROLLBAR_SIZE;


// width of area used for resizing (the grip at the end of a note)
const int RESIZE_AREA_WIDTH = 9;

// width of line for setting volume/panning of note
const int NOTE_EDIT_LINE_WIDTH = 3;

// key where to start
const int INITIAL_START_KEY = Key_C + Octave_4 * KeysPerOctave;

// number of each note to provide in quantization and note lengths
const int NUM_EVEN_LENGTHS = 6;
const int NUM_TRIPLET_LENGTHS = 5;



QPixmap * PianoRoll::s_toolDraw = NULL;
QPixmap * PianoRoll::s_toolErase = NULL;
QPixmap * PianoRoll::s_toolSelect = NULL;
QPixmap * PianoRoll::s_toolMove = NULL;
QPixmap * PianoRoll::s_toolOpen = NULL;
QPixmap* PianoRoll::s_toolKnife = nullptr;

TextFloat * PianoRoll::s_textFloat = NULL;

static QString s_noteStrings[12] = {"C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"};

static QString getNoteString(int key)
{
	return s_noteStrings[key % 12] + QString::number(static_cast<int>(FirstOctave + key / KeysPerOctave));
}

// used for drawing of piano
PianoRoll::PianoRollKeyTypes PianoRoll::prKeyOrder[] =
{
	PR_WHITE_KEY_SMALL, PR_BLACK_KEY, PR_WHITE_KEY_BIG, PR_BLACK_KEY,
	PR_WHITE_KEY_SMALL, PR_WHITE_KEY_SMALL, PR_BLACK_KEY, PR_WHITE_KEY_BIG,
	PR_BLACK_KEY, PR_WHITE_KEY_BIG, PR_BLACK_KEY, PR_WHITE_KEY_SMALL
} ;


const int DEFAULT_PR_PPB = DEFAULT_CELL_WIDTH * DefaultStepsPerBar;

const QVector<float> PianoRoll::m_zoomLevels =
		{0.125f, 0.25f, 0.5f, 1.0f, 1.5f, 2.0f, 4.0f, 8.0f};

const QVector<float> PianoRoll::m_zoomYLevels =
		{0.25f, 0.5f, 1.0f, 1.5f, 2.0f, 2.5f, 3.0f, 4.0f};


PianoRoll::PianoRoll() :
	m_nemStr( QVector<QString>() ),
	m_noteEditMenu( NULL ),
	m_semiToneMarkerMenu( NULL ),
	m_zoomingModel(),
	m_zoomingYModel(),
	m_quantizeModel(),
	m_noteLenModel(),
	m_scaleModel(),
	m_chordModel(),
	m_pattern( NULL ),
	m_currentPosition(),
	m_recording( false ),
	m_currentNote( NULL ),
	m_action( ActionNone ),
	m_noteEditMode( NoteEditVolume ),
	m_notesEditHeight( 100 ),
	m_userSetNotesEditHeight(100),
	m_ppb( DEFAULT_PR_PPB ),
	m_keyLineHeight(DEFAULT_KEY_LINE_HEIGHT),
	m_whiteKeySmallHeight(qFloor(m_keyLineHeight * 1.5)),
	m_whiteKeyBigHeight(m_keyLineHeight * 2),
	m_blackKeyHeight(m_keyLineHeight),
	m_lenOfNewNotes( TimePos( 0, DefaultTicksPerBar/4 ) ),
	m_lastNoteVolume( DefaultVolume ),
	m_lastNotePanning( DefaultPanning ),
	m_minResizeLen( 0 ),
	m_startKey( INITIAL_START_KEY ),
	m_lastKey( 0 ),
	m_editMode( ModeDraw ),
	m_lastEditMode( m_editMode ),
	m_scrollBack( false ),
	m_stepRecorderWidget(this, DEFAULT_PR_PPB, PR_TOP_MARGIN, PR_BOTTOM_MARGIN + m_notesEditHeight, WHITE_KEY_WIDTH, 0),
	m_stepRecorder(*this, m_stepRecorderWidget),
	m_barLineColor( 0, 0, 0 ),
	m_beatLineColor( 0, 0, 0 ),
	m_lineColor( 0, 0, 0 ),
	m_noteModeColor( 0, 0, 0 ),
	m_noteColor( 0, 0, 0 ),
	m_ghostNoteColor( 0, 0, 0 ),
	m_ghostNoteTextColor( 0, 0, 0 ),
	m_barColor( 0, 0, 0 ),
	m_selectedNoteColor( 0, 0, 0 ),
	m_textColor( 0, 0, 0 ),
	m_textColorLight( 0, 0, 0 ),
	m_textShadow( 0, 0, 0 ),
	m_markedSemitoneColor( 0, 0, 0 ),
	m_knifeCutLineColor(0, 0, 0),
	m_noteOpacity( 255 ),
	m_ghostNoteOpacity( 255 ),
	m_noteBorders( true ),
	m_ghostNoteBorders( true ),
	m_backgroundShade( 0, 0, 0 ),
	m_whiteKeyWidth(WHITE_KEY_WIDTH),
	m_blackKeyWidth(BLACK_KEY_WIDTH)
{
	// gui names of edit modes
	m_nemStr.push_back( tr( "Note Velocity" ) );
	m_nemStr.push_back( tr( "Note Panning" ) );

	m_noteEditMenu = new QMenu( this );
	m_noteEditMenu->clear();
	for( int i = 0; i < m_nemStr.size(); ++i )
	{
		QAction * act = new QAction( m_nemStr.at(i), this );
		connect( act, &QAction::triggered, [this, i](){ changeNoteEditMode(i); } );
		m_noteEditMenu->addAction( act );
	}

	m_semiToneMarkerMenu = new QMenu( this );

	QAction* markSemitoneAction = new QAction( tr("Mark/unmark current semitone"), this );
	QAction* markAllOctaveSemitonesAction = new QAction( tr("Mark/unmark all corresponding octave semitones"), this );
	QAction* markScaleAction = new QAction( tr("Mark current scale"), this );
	QAction* markChordAction = new QAction( tr("Mark current chord"), this );
	QAction* unmarkAllAction = new QAction( tr("Unmark all"), this );
	QAction* copyAllNotesAction = new QAction( tr("Select all notes on this key"), this);

	connect( markSemitoneAction, &QAction::triggered, [this](){ markSemiTone(stmaMarkCurrentSemiTone); });
	connect( markAllOctaveSemitonesAction, &QAction::triggered, [this](){ markSemiTone(stmaMarkAllOctaveSemiTones); });
	connect( markScaleAction, &QAction::triggered, [this](){ markSemiTone(stmaMarkCurrentScale); });
	connect( markChordAction, &QAction::triggered, [this](){ markSemiTone(stmaMarkCurrentChord); });
	connect( unmarkAllAction, &QAction::triggered, [this](){ markSemiTone(stmaUnmarkAll); });
	connect( copyAllNotesAction, &QAction::triggered, [this](){ markSemiTone(stmaCopyAllNotesOnKey); });

	markScaleAction->setEnabled( false );
	markChordAction->setEnabled( false );

	connect( this, SIGNAL(semiToneMarkerMenuScaleSetEnabled(bool)), markScaleAction, SLOT(setEnabled(bool)) );
	connect( this, SIGNAL(semiToneMarkerMenuChordSetEnabled(bool)), markChordAction, SLOT(setEnabled(bool)) );

	m_semiToneMarkerMenu->addAction( markSemitoneAction );
	m_semiToneMarkerMenu->addAction( markAllOctaveSemitonesAction );
	m_semiToneMarkerMenu->addAction( markScaleAction );
	m_semiToneMarkerMenu->addAction( markChordAction );
	m_semiToneMarkerMenu->addAction( unmarkAllAction );
	m_semiToneMarkerMenu->addAction( copyAllNotesAction );

	// init pixmaps
	if( s_toolDraw == NULL )
	{
		s_toolDraw = new QPixmap( embed::getIconPixmap( "edit_draw" ) );
	}
	if( s_toolErase == NULL )
	{
		s_toolErase= new QPixmap( embed::getIconPixmap( "edit_erase" ) );
	}
	if( s_toolSelect == NULL )
	{
		s_toolSelect = new QPixmap( embed::getIconPixmap( "edit_select" ) );
	}
	if( s_toolMove == NULL )
	{
		s_toolMove = new QPixmap( embed::getIconPixmap( "edit_move" ) );
	}
	if( s_toolOpen == NULL )
	{
		s_toolOpen = new QPixmap( embed::getIconPixmap( "automation" ) );
	}
	if (s_toolKnife == nullptr)
	{
		s_toolKnife = new QPixmap(embed::getIconPixmap("edit_knife"));
	}

	// init text-float
	if( s_textFloat == NULL )
	{
		s_textFloat = new TextFloat;
	}

	setAttribute( Qt::WA_OpaquePaintEvent, true );

	// add time-line
	m_timeLine = new TimeLineWidget(m_whiteKeyWidth, 0, m_ppb,
					Engine::getSong()->getPlayPos(
						Song::Mode_PlayPattern ),
						m_currentPosition,
						Song::Mode_PlayPattern, this );
	connect( this, SIGNAL( positionChanged( const TimePos & ) ),
		m_timeLine, SLOT( updatePosition( const TimePos & ) ) );
	connect( m_timeLine, SIGNAL( positionChanged( const TimePos & ) ),
			this, SLOT( updatePosition( const TimePos & ) ) );
	connect( m_timeLine, SIGNAL(regionSelectedFromPixels(int, int)),
			this, SLOT(selectRegionFromTimeline(int, int)));
	connect(m_timeLine, SIGNAL(selectionFinished()), this, SLOT(finishSelectFromTimeline()));

	// white position line follows timeline marker
	m_positionLine = new PositionLine(this);

	//update timeline when in step-recording mode
	connect( &m_stepRecorderWidget, SIGNAL( positionChanged( const TimePos & ) ),
			this, SLOT( updatePositionStepRecording( const TimePos & ) ) );

	// update timeline when in record-accompany mode
	connect( Engine::getSong()->getPlayPos( Song::Mode_PlaySong ).m_timeLine,
				SIGNAL( positionChanged( const TimePos & ) ),
			this,
			SLOT( updatePositionAccompany( const TimePos & ) ) );
	// TODO
/*	connect( engine::getSong()->getPlayPos( Song::Mode_PlayBB ).m_timeLine,
				SIGNAL( positionChanged( const TimePos & ) ),
			this,
			SLOT( updatePositionAccompany( const TimePos & ) ) );*/

	// init scrollbars
	m_leftRightScroll = new QScrollBar( Qt::Horizontal, this );
	m_leftRightScroll->setSingleStep( 1 );
	connect( m_leftRightScroll, SIGNAL( valueChanged( int ) ), this,
						SLOT( horScrolled( int ) ) );

	m_topBottomScroll = new QScrollBar( Qt::Vertical, this );
	m_topBottomScroll->setSingleStep( 1 );
	m_topBottomScroll->setPageStep( 20 );
	connect( m_topBottomScroll, SIGNAL( valueChanged( int ) ), this,
						SLOT( verScrolled( int ) ) );

	// setup zooming-stuff
	for( float const & zoomLevel : m_zoomLevels )
	{
		m_zoomingModel.addItem( QString( "%1\%" ).arg( zoomLevel * 100 ) );
	}
	m_zoomingModel.setValue( m_zoomingModel.findText( "100%" ) );
	connect( &m_zoomingModel, SIGNAL( dataChanged() ),
					this, SLOT( zoomingChanged() ) );

	// zoom y
	for (float const & zoomLevel : m_zoomYLevels)
	{
		m_zoomingYModel.addItem(QString( "%1\%" ).arg(zoomLevel * 100));
	}
	m_zoomingYModel.setValue(m_zoomingYModel.findText("100%"));
	connect(&m_zoomingYModel, SIGNAL(dataChanged()),
					this, SLOT(zoomingYChanged()));

	// Set up quantization model
	m_quantizeModel.addItem( tr( "Note lock" ) );
	for (auto q : Quantizations) {
		m_quantizeModel.addItem(QString("1/%1").arg(q));
	}
	m_quantizeModel.setValue( m_quantizeModel.findText( "1/16" ) );

	connect( &m_quantizeModel, SIGNAL( dataChanged() ),
					this, SLOT( quantizeChanged() ) );

	// Set up note length model
	m_noteLenModel.addItem( tr( "Last note" ),
					std::make_unique<PixmapLoader>( "edit_draw" ) );
	const QString pixmaps[] = { "whole", "half", "quarter", "eighth",
						"sixteenth", "thirtysecond", "triplethalf",
						"tripletquarter", "tripleteighth",
						"tripletsixteenth", "tripletthirtysecond" } ;

	for( int i = 0; i < NUM_EVEN_LENGTHS; ++i )
	{
		auto loader = std::make_unique<PixmapLoader>( "note_" + pixmaps[i] );
		m_noteLenModel.addItem( "1/" + QString::number( 1 << i ), ::move(loader) );
	}
	for( int i = 0; i < NUM_TRIPLET_LENGTHS; ++i )
	{
		auto loader = std::make_unique<PixmapLoader>( "note_" + pixmaps[i+NUM_EVEN_LENGTHS] );
		m_noteLenModel.addItem( "1/" + QString::number( (1 << i) * 3 ), ::move(loader) );
	}
	m_noteLenModel.setValue( 0 );

	// Note length change can cause a redraw if Q is set to lock
	connect( &m_noteLenModel, SIGNAL( dataChanged() ),
					this, SLOT( noteLengthChanged() ) );

	// Set up key selection dropdown
	m_keyModel.addItem(tr("No key"));
	// Use piano roll note strings for key dropdown
	for (int i = 0; i < 12; i++) { m_keyModel.addItem(s_noteStrings[i]); }
	m_keyModel.setValue(0); // start with "No key"
	connect(&m_keyModel, &ComboBoxModel::dataChanged, this, &PianoRoll::keyChanged);

	// Set up scale model
	auto chord_table = InstrumentFunctionNoteStacking::ChordTable::getInstance();

	m_scaleModel.addItem( tr("No scale") );
	for( const InstrumentFunctionNoteStacking::Chord& chord : chord_table )
	{
		if( chord.isScale() )
		{
			m_scaleModel.addItem( chord.getName() );
		}
	}

	m_scaleModel.setValue( 0 );
	// connect scale change to key change so it auto-highlights with scale as well
	connect(&m_scaleModel, &ComboBoxModel::dataChanged, this, &PianoRoll::keyChanged);
	// change can update m_semiToneMarkerMenu
	connect( &m_scaleModel, SIGNAL( dataChanged() ),
						this, SLOT( updateSemiToneMarkerMenu() ) );

	// Set up chord model
	m_chordModel.addItem( tr("No chord") );
	for( const InstrumentFunctionNoteStacking::Chord& chord : chord_table )
	{
		if( ! chord.isScale() )
		{
			m_chordModel.addItem( chord.getName() );
		}
	}

	m_chordModel.setValue( 0 );

	// change can update m_semiToneMarkerMenu
	connect( &m_chordModel, SIGNAL( dataChanged() ),
					this, SLOT( updateSemiToneMarkerMenu() ) );

	setFocusPolicy( Qt::StrongFocus );
	setFocus();
	setMouseTracking( true );

	connect( &m_scaleModel, SIGNAL( dataChanged() ),
					this, SLOT( updateSemiToneMarkerMenu() ) );

	connect( Engine::getSong(), SIGNAL( timeSignatureChanged( int, int ) ),
						this, SLOT( update() ) );

	// Set up snap model
	m_snapModel.addItem(tr("Nudge"));
	m_snapModel.addItem(tr("Snap"));
	m_snapModel.setValue(0);
	changeSnapMode();
	connect(&m_snapModel, SIGNAL(dataChanged()),
		this, SLOT(changeSnapMode()));

	m_stepRecorder.initialize();

	m_lastChord = nullptr;
}



void PianoRoll::reset()
{
	m_lastNoteVolume = DefaultVolume;
	m_lastNotePanning = DefaultPanning;
	clearGhostPattern();
}

void PianoRoll::showTextFloat(const QString &text, const QPoint &pos, int timeout)
{
	s_textFloat->setText( text );
	// show the float, offset slightly so as to not obscure anything
	s_textFloat->moveGlobal( this, pos + QPoint(4, 16) );
	if (timeout == -1)
	{
		s_textFloat->show();
	}
	else
	{
		s_textFloat->setVisibilityTimeOut( timeout );
	}
}


void PianoRoll::showVolTextFloat(volume_t vol, const QPoint &pos, int timeout)
{
	//! \todo display velocity for MIDI-based instruments
	// possibly dBFS values too? not sure if it makes sense for note volumes...
	showTextFloat( tr("Velocity: %1%").arg( vol ), pos, timeout );
}


void PianoRoll::showPanTextFloat(panning_t pan, const QPoint &pos, int timeout)
{
	QString text;
	if( pan < 0 )
	{
		text = tr("Panning: %1% left").arg( qAbs( pan ) );
	}
	else if( pan > 0 )
	{
		text = tr("Panning: %1% right").arg( qAbs( pan ) );
	}
	else
	{
		text = tr("Panning: center");
	}
	showTextFloat( text, pos, timeout );
}



void PianoRoll::changeNoteEditMode( int i )
{
	m_noteEditMode = (NoteEditMode) i;
	repaint();
}


void PianoRoll::markSemiTone(int i, bool fromMenu)
{
	const int key = fromMenu ? m_hoverKey : m_keyModel.value() - 1;
	const InstrumentFunctionNoteStacking::Chord * chord = nullptr;
	auto cti = InstrumentFunctionNoteStacking::ChordTable::getInstance();

	// if "No key" is selected, key is -1, unmark all semitones
	// or if scale changed from toolbar to "No scale", unmark all semitones
	if (!fromMenu && (key < 0 || m_scaleModel.value() == 0)) { i = stmaUnmarkAll; }

	switch( static_cast<SemiToneMarkerAction>( i ) )
	{
		case stmaUnmarkAll:
			m_markedSemiTones.clear();
			break;
		case stmaMarkCurrentSemiTone:
		{
			QList<int>::iterator it = std::find( m_markedSemiTones.begin(), m_markedSemiTones.end(), key );
			if( it != m_markedSemiTones.end() )
			{
				m_markedSemiTones.erase( it );
			}
			else
			{
				m_markedSemiTones.push_back( key );
			}
			break;
		}
		case stmaMarkAllOctaveSemiTones:
		{
			QList<int> aok = getAllOctavesForKey(key);

			if ( m_markedSemiTones.contains(key) )
			{
				// lets erase all of the ones that match this by octave
				QList<int>::iterator i;
				for (int ix = 0; ix < aok.size(); ++ix)
				{
					i = std::find(m_markedSemiTones.begin(), m_markedSemiTones.end(), aok.at(ix));
					if (i != m_markedSemiTones.end())
					{
						m_markedSemiTones.erase(i);
					}
				}
			}
			else
			{
				// we should add all of the ones that match this by octave
				m_markedSemiTones.append(aok);
			}

			break;
		}
		case stmaMarkCurrentScale:
			chord = &cti.getScaleByName(m_scaleModel.currentText());
		case stmaMarkCurrentChord:
		{
			if( ! chord )
			{
				chord = &cti.getChordByName(m_chordModel.currentText());
			}

			if( chord->isEmpty() )
			{
				break;
			}
			else if( chord->isScale() )
			{
				m_markedSemiTones.clear();
			}

			const int first = chord->isScale() ? 0 : key;
			const int last = chord->isScale() ? NumKeys : key + chord->last();
			const int cap = ( chord->isScale() || chord->last() == 0 ) ? KeysPerOctave : chord->last();

			for( int i = first; i <= last; i++ )
			{
			  if( chord->hasSemiTone( ( i + cap - ( key % cap ) ) % cap ) )
				{
					m_markedSemiTones.push_back( i );
				}
			}
			break;
		}
		case stmaCopyAllNotesOnKey:
		{
			selectNotesOnKey();
			break;
		}
		default:
			;
	}

	std::sort( m_markedSemiTones.begin(), m_markedSemiTones.end(), std::greater<int>() );
	QList<int>::iterator new_end = std::unique( m_markedSemiTones.begin(), m_markedSemiTones.end() );
	m_markedSemiTones.erase( new_end, m_markedSemiTones.end() );
	// until we move the mouse the window won't update, force redraw
	update();
}


PianoRoll::~PianoRoll()
{
}


void PianoRoll::setGhostPattern( Pattern* newPattern )
{
	// Expects a pointer to a pattern or nullptr.
	m_ghostNotes.clear();
	if( newPattern != nullptr )
	{
		for( Note *note : newPattern->notes() )
		{
			Note * new_note = new Note( note->length(), note->pos(), note->key() );
			m_ghostNotes.push_back( new_note );
		}
		emit ghostPatternSet( true );
	}
}


void PianoRoll::loadGhostNotes( const QDomElement & de )
{
	// Load ghost notes from DOM element.
	if( de.isElement() )
	{
		QDomNode node = de.firstChild();
		while( !node.isNull() )
		{
			Note * n = new Note;
			n->restoreState( node.toElement() );
			n->setVolume(DefaultVolume);
			m_ghostNotes.push_back( n );
			node = node.nextSibling();
		}
		emit ghostPatternSet( true );
	}
}


void PianoRoll::clearGhostPattern()
{
	setGhostPattern( nullptr );
	emit ghostPatternSet( false );
	update();
}


void PianoRoll::glueNotes()
{
	if (hasValidPattern())
	{
		NoteVector selectedNotes = getSelectedNotes();
		if (selectedNotes.empty())
		{
			TextFloat::displayMessage( tr( "Glue notes failed" ),
					tr( "Please select notes to glue first." ),
					embed::getIconPixmap( "glue", 24, 24 ),
					3000 );
			return;
		}

		// Make undo possible
		m_pattern->addJournalCheckPoint();

		// Sort notes on key and then pos.
		std::sort(selectedNotes.begin(), selectedNotes.end(),
			[](const Note * note, const Note * compareNote) -> bool
			{
				if (note->key() == compareNote->key())
				{
					return note->pos() < compareNote->pos();
				}
				return note->key() < compareNote->key();
			});

		QList<Note *> noteToRemove;

		NoteVector::iterator note = selectedNotes.begin();
		auto nextNote = note+1;
		NoteVector::iterator end = selectedNotes.end();

		while (note != end && nextNote != end)
		{
			// key and position match for glue. The notes are already
			// sorted so we don't need to test that nextNote is the same
			// position or next in sequence.
			if ((*note)->key() == (*nextNote)->key()
				&& (*nextNote)->pos() <= (*note)->pos()
				+ qMax(TimePos(0), (*note)->length()))
			{
				(*note)->setLength(qMax((*note)->length(),
					TimePos((*nextNote)->endPos() - (*note)->pos())));
				noteToRemove.push_back(*nextNote);
				++nextNote;
			}
			// key or position doesn't match
			else
			{
				note = nextNote;
				nextNote = note+1;
			}
		}

		// Remove old notes
		for (int i = 0; i < noteToRemove.count(); ++i)
		{
			m_pattern->removeNote(noteToRemove[i]);
		}

		update();
	}
}

void PianoRoll::fitNoteLengths(bool fill)
{
	if (!hasValidPattern()) { return; }
	m_pattern->addJournalCheckPoint();

	// Reference notes
	NoteVector refNotes = m_pattern->notes();
	std::sort(refNotes.begin(), refNotes.end(), Note::lessThan);

	// Notes to edit
	NoteVector notes = getSelectedNotes();
	if (notes.empty())
	{
		notes = refNotes;
	}
	else if (!fill)
	{
		std::sort(notes.begin(), notes.end(), Note::lessThan);
	}
	if (fill)
	{
		std::sort(notes.begin(), notes.end(), [](Note* n1, Note* n2) { return n1->endPos() < n2->endPos(); });
	}

	int length;
	NoteVector::iterator ref = refNotes.begin();
	for (Note* note : notes)
	{
		// Fast forward to next reference note
		while (ref != refNotes.end() && (fill ? (*ref)->pos() < note->endPos() : (*ref)->pos() <= note->pos()))
		{
			ref++;
		}
		if (ref == refNotes.end())
		{
			if (!fill) { break; }
			// Last notes stretch to end of last bar
			length = notes.last()->endPos().nextFullBar() * TimePos::ticksPerBar() - note->pos();
		}
		else
		{
			length = (*ref)->pos() - note->pos();
		}
		if (fill ? note->length() < length : note->length() > length)
		{
			note->setLength(length);
		}
	}

	update();
	gui->songEditor()->update();
	Engine::getSong()->setModified();
}


void PianoRoll::constrainNoteLengths(bool constrainMax)
{
	if (!hasValidPattern()) { return; }
	m_pattern->addJournalCheckPoint();

	NoteVector notes = getSelectedNotes();
	if (notes.empty())
	{
		notes = m_pattern->notes();
	}

	TimePos bound = m_lenOfNewNotes;  // will be length of last note
	for (Note* note : notes)
	{
		if (constrainMax ? note->length() > bound : note->length() < bound)
		{
			note->setLength(bound);
		}
	}

	update();
	gui->songEditor()->update();
	Engine::getSong()->setModified();
}


void PianoRoll::loadMarkedSemiTones(const QDomElement & de)
{
	// clear marked semitones to prevent leftover marks
	m_markedSemiTones.clear();
	if (de.isElement())
	{
		QDomNode node = de.firstChild();
		while (!node.isNull())
		{
			bool ok;
			int key = node.toElement().attribute(
				QString("key"), QString("-1")).toInt(&ok, 10);
			if (ok && key >= 0)
			{
				m_markedSemiTones.append(key);
			}
			node = node.nextSibling();
		}
	}
	// from markSemiTone, required otherwise marks will not show
	std::sort(m_markedSemiTones.begin(), m_markedSemiTones.end(), std::greater<int>());
	QList<int>::iterator new_end = std::unique(m_markedSemiTones.begin(), m_markedSemiTones.end());
	m_markedSemiTones.erase(new_end, m_markedSemiTones.end());
}


void PianoRoll::setCurrentPattern( Pattern* newPattern )
{
	if( hasValidPattern() )
	{
		m_pattern->instrumentTrack()->disconnect( this );
	}

	// force the song-editor to stop playing if it played pattern before
	if( Engine::getSong()->isPlaying() &&
		Engine::getSong()->playMode() == Song::Mode_PlayPattern )
	{
		Engine::getSong()->playPattern( NULL );
	}

	if(m_stepRecorder.isRecording())
	{
		m_stepRecorder.stop();
	}

	// set new data
	m_pattern = newPattern;
	m_currentPosition = 0;
	m_currentNote = NULL;
	m_startKey = INITIAL_START_KEY;

	m_stepRecorder.setCurrentPattern(newPattern);

	if( ! hasValidPattern() )
	{
		//resizeEvent( NULL );

		update();
		emit currentPatternChanged();
		return;
	}

	m_leftRightScroll->setValue( 0 );

	// determine the central key so that we can scroll to it
	int central_key = 0;
	int total_notes = 0;
	for( const Note *note : m_pattern->notes() )
	{
		if( note->length() > 0 )
		{
			central_key += note->key();
			++total_notes;
		}
	}

	if (total_notes > 0)
	{
		central_key = central_key / total_notes - (NumKeys - m_totalKeysToScroll) / 2;
		m_startKey = qBound(0, central_key, NumKeys);
	}

	// resizeEvent() does the rest for us (scrolling, range-checking
	// of start-notes and so on...)
	resizeEvent( NULL );

	// make sure to always get informed about the pattern being destroyed
	connect( m_pattern, SIGNAL( destroyedPattern( Pattern* ) ), this, SLOT( hidePattern( Pattern* ) ) );

	connect( m_pattern->instrumentTrack(), SIGNAL( midiNoteOn( const Note& ) ), this, SLOT( startRecordNote( const Note& ) ) );
	connect( m_pattern->instrumentTrack(), SIGNAL( midiNoteOff( const Note& ) ), this, SLOT( finishRecordNote( const Note& ) ) );
	connect( m_pattern->instrumentTrack()->pianoModel(), SIGNAL( dataChanged() ), this, SLOT( update() ) );

	connect(m_pattern->instrumentTrack()->firstKeyModel(), SIGNAL(dataChanged()), this, SLOT(update()));
	connect(m_pattern->instrumentTrack()->lastKeyModel(), SIGNAL(dataChanged()), this, SLOT(update()));

	update();
	emit currentPatternChanged();
}



void PianoRoll::hidePattern( Pattern* pattern )
{
	if( m_pattern == pattern )
	{
		setCurrentPattern( NULL );
	}
}

void PianoRoll::selectRegionFromTimeline( int xStart, int xEnd )
{
	int startTick = getTick(xStart);
	int endTick = getTick(xEnd);

	// FIXME if ctrl-drag on timeline is interrupted by right click,
	// ActionSelectNotes will remain until next mouse click
	m_action = ActionSelectNotes;

	// override mouse position to fake a selection from bottom to top
	m_mouseDownTick = startTick;
	m_hoverTick = endTick;
	m_mouseDownKey = 0;
	m_hoverKey = NumKeys - 1;

	update();
}




void PianoRoll::finishSelectFromTimeline()
{
	computeSelectedNotes();
	endDragAction();
}




void PianoRoll::drawNoteRect( QPainter & p, const Note * n, const QColor & noteCol, const QColor & noteTextColor,
				const QColor & selCol, const int noteOpc, const bool borders, bool drawNoteName )
{
	if (n->length() == 0) { return; }

	// drum notes are displayed as 4 ticks
	int endTick = n->length() < 0
					? n->pos().getTicks() + 4
					: n->endPos().getTicks();

	// vertical grid lines are drawn at the left-most pixel of note, so we move it by 1
	int x = xCoordOfTick(n->pos()) + 1;
	int y = yCoordOfKey(n->key());
	int width = std::max(2, xCoordOfTick(endTick) - x);

	// return if note is outside visible area
	if (getPianoRollAreaIn(x, y) != PianoRollArea::Notes
		&& getPianoRollAreaIn(x + width, y) != PianoRollArea::Notes)
	{
		return;
	}

	// Volume
	float const volumeRange = static_cast<float>(MaxVolume - MinVolume);
	float const volumeSpan = static_cast<float>(n->getVolume() - MinVolume);
	float const volumeRatio = volumeSpan / volumeRange;
	int volVal = qMin( 255, 100 + static_cast<int>( volumeRatio * 155.0f) );

	// Panning
	float const panningRange = static_cast<float>(PanningRight - PanningLeft);
	float const leftPanSpan = static_cast<float>(PanningRight - n->getPanning());
	float const rightPanSpan = static_cast<float>(n->getPanning() - PanningLeft);

	float leftPercent = qMin<float>( 1.0f, leftPanSpan / panningRange * 2.0f );
	float rightPercent = qMin<float>( 1.0f, rightPanSpan / panningRange * 2.0f );

	QColor col = QColor( noteCol );
	QPen pen;

	if( n->selected() )
	{
		col = QColor( selCol );
	}

	const int borderWidth = borders ? 1 : 0;
	// horizontal grid lines are drawn at bottom-most pixel of note so we cut height by 1
	const int noteHeight = m_keyLineHeight - 1 - borderWidth;
	int noteWidth = width - borderWidth;

	// adjust note to make it a bit faded if it has a lower volume
	// in stereo using gradients
	QColor lcol = QColor::fromHsv( col.hue(), col.saturation(),
				       static_cast<int>(volVal * leftPercent), noteOpc );
	QColor rcol = QColor::fromHsv( col.hue(), col.saturation(),
				       static_cast<int>(volVal * rightPercent), noteOpc );

	QLinearGradient gradient( x, y, x, y + noteHeight );
	gradient.setColorAt( 0, rcol );
	gradient.setColorAt( 1, lcol );
	p.setBrush( gradient );

	if ( borders )
	{
		p.setPen( col );
	}
	else
	{
		p.setPen( Qt::NoPen );
	}

	p.drawRect( x, y, noteWidth, noteHeight );

	// Draw note key text
	if (drawNoteName)
	{
		p.save();
		int const noteTextHeight = static_cast<int>(noteHeight * 0.8);
		if (noteTextHeight > 6)
		{
			QString noteKeyString = getNoteString(n->key());

			QFont noteFont(p.font());
			noteFont.setPixelSize(noteTextHeight);
			QFontMetrics fontMetrics(noteFont);
			QSize textSize = fontMetrics.size(Qt::TextSingleLine, noteKeyString);

			int const distanceToBorder = 2;
			int const xOffset = borderWidth + distanceToBorder;

			// noteTextHeight, textSize are not suitable for determining vertical spacing,
			// capHeight() can be used for this, but requires Qt 5.8.
			// We use boundingRect() with QChar (the QString version returns wrong value).
			QRect const boundingRect = fontMetrics.boundingRect(QChar::fromLatin1('H'));
			int const yOffset = (noteHeight - boundingRect.top() - boundingRect.bottom()) / 2;

			if (textSize.width() < noteWidth - xOffset)
			{
				p.setPen(noteTextColor);
				p.setFont(noteFont);
				QPoint textStart(x + xOffset, y + yOffset);

				p.drawText(textStart, noteKeyString);
			}
		}
		p.restore();
	}

	// draw the note endmark, to hint the user to resize
	p.setBrush( col );
	if( width > 2 )
	{
		const int endmarkWidth = 3 - borderWidth;
		p.drawRect( x + noteWidth - endmarkWidth, y, endmarkWidth, noteHeight );
	}
}




void PianoRoll::drawDetuningInfo( QPainter & _p, const Note * _n, int _x,
								int _y ) const
{
	int middle_y = _y + m_keyLineHeight / 2;
	_p.setPen(m_noteColor);
	_p.setClipRect(
		m_whiteKeyWidth,
		PR_TOP_MARGIN,
		noteAreaWidth(),
		keyAreaBottom() - keyAreaTop());

	// Draw lines for the detuning automation, treating cubic hermit curves
	// as straight lines for now. Also draw discrete jumps.
	int old_x = 0;
	int old_y = 0;

	timeMap & map = _n->detuning()->automationPattern()->getTimeMap();
	for (timeMap::const_iterator it = map.begin(); it != map.end(); ++it)
	{
		// Current node values
		int cur_ticks = POS(it);
		int cur_x = _x + cur_ticks * m_ppb / TimePos::ticksPerBar();
		const float cur_level = INVAL(it);
		int cur_y = middle_y - cur_level * m_keyLineHeight;

		// First line to represent the inValue of the first node
		if (it == map.begin())
		{
			_p.drawLine(cur_x - 1, cur_y, cur_x + 1, cur_y);
			_p.drawLine(cur_x, cur_y - 1, cur_x, cur_y + 1);
		}
		// All subsequent lines will take the outValue of the previous node
		// and the inValue of the current node. It will also draw a vertical
		// line if there was a discrete jump (from old_x,old_y to pre_x,pre_y)
		else
		{
			// Previous node values (based on outValue). We just calculate
			// the y level because the x will be the same as old_x.
			const float pre_level = OUTVAL(it - 1);
			int pre_y = middle_y - pre_level * m_keyLineHeight;

			// Draws the line representing the discrete jump if there's one
			if (old_y != pre_y)
			{
				_p.drawLine(old_x, old_y, old_x, pre_y);
			}

			// Now draw the lines representing the actual progression from one
			// node to the other
			switch (_n->detuning()->automationPattern()->progressionType())
			{
				case AutomationPattern::DiscreteProgression:
					_p.drawLine(old_x, pre_y, cur_x, pre_y);
					_p.drawLine(cur_x, pre_y, cur_x, cur_y);
					break;
				case AutomationPattern::CubicHermiteProgression: /* TODO */
				case AutomationPattern::LinearProgression:
					_p.drawLine(old_x, pre_y, cur_x, cur_y);
					break;
			}

			// If we are in the last node and there's a discrete jump, we draw a
			// vertical line representing it
			if ((it + 1) == map.end())
			{
				const float last_level = OUTVAL(it);
				if (cur_level != last_level)
				{
					int last_y = middle_y - last_level * m_keyLineHeight;
					_p.drawLine(cur_x, cur_y, cur_x, last_y);
				}
			}
		}

		old_x = cur_x;
		old_y = cur_y;
	}
}




void PianoRoll::clearSelectedNotes()
{
	if( m_pattern != NULL )
	{
		for( Note *note : m_pattern->notes() )
		{
			note->setSelected( false );
		}
	}
}



void PianoRoll::shiftSemiTone(int amount) //Shift notes by amount semitones
{
	if (!hasValidPattern()) { return; }

	auto selectedNotes = getSelectedNotes();
	//If no notes are selected, shift all of them, otherwise shift selection
	if (selectedNotes.empty()) { return shiftSemiTone(m_pattern->notes(), amount); }
	else { return shiftSemiTone(selectedNotes, amount); }
}

void PianoRoll::shiftSemiTone(NoteVector notes, int amount)
{
	m_pattern->addJournalCheckPoint();
	for (Note *note : notes) { note->setKey( note->key() + amount ); }

	m_pattern->rearrangeAllNotes();
	m_pattern->dataChanged();
	//We modified the song
	update();
	gui->songEditor()->update();
}




void PianoRoll::shiftPos(int amount) //Shift notes pos by amount
{
	if (!hasValidPattern()) { return; }

	auto selectedNotes = getSelectedNotes();
	//If no notes are selected, shift all of them, otherwise shift selection
	if (selectedNotes.empty()) { return shiftPos(m_pattern->notes(), amount); }
	else { return shiftPos(selectedNotes, amount); }
}

void PianoRoll::shiftPos(NoteVector notes, int amount)
{
	m_pattern->addJournalCheckPoint();
	auto leftMostPos = notes.first()->pos();
	//Limit leftwards shifts to prevent moving left of pattern start
	auto shiftAmount = (leftMostPos > -amount) ? amount : -leftMostPos;
	if (shiftAmount == 0) { return; }

	for (Note *note : notes) { note->setPos( note->pos() + shiftAmount ); }

	m_pattern->rearrangeAllNotes();
	m_pattern->updateLength();
	m_pattern->dataChanged();
	// we modified the song
	update();
	gui->songEditor()->update();
}




bool PianoRoll::isSelection() const // are any notes selected?
{
	for( const Note *note : m_pattern->notes() )
	{
		if( note->selected() )
		{
			return true;
		}
	}

	return false;
}



int PianoRoll::selectionCount() const // how many notes are selected?
{
	return getSelectedNotes().size();
}



void PianoRoll::keyPressEvent(QKeyEvent* ke)
{
	if (!hasValidPattern()) { return; }

	if(m_stepRecorder.isRecording())
	{
		bool handled = m_stepRecorder.keyPressEvent(ke);
		if(handled)
		{
			ke->accept();
			update();
			return;
		}
	}

	m_ctrlPressed = ke->modifiers() & Qt::ControlModifier;
	m_shiftPressed = ke->modifiers() & Qt::ShiftModifier;
	m_altPressed = ke->modifiers() & Qt::AltModifier;

	// -- The following actions can safely be performed during a mouse drag action

	if (ke->modifiers() == Qt::NoModifier)
	{
		const int key_num = PianoView::getKeyFromKeyEvent( ke ) + ( DefaultOctave - 1 ) * KeysPerOctave;

		if (!ke->isAutoRepeat() && key_num > -1)
		{
			m_pattern->instrumentTrack()->pianoModel()->handleKeyPress(key_num);
			//  if a chord is set, play all chord notes (simulate click on all):
			playChordNotes(key_num);
			ke->accept();
		}
	}

	switch( ke->key() )
	{
		case Qt::Key_Up:
		case Qt::Key_Down:
			{
				int direction = (ke->key() == Qt::Key_Up ? +1 : -1);
				if (ke->modifiers() == Qt::NoModifier)
				{
					// scroll
					m_topBottomScroll->setValue( m_topBottomScroll->value() -
						cm_scrollAmtVert * direction );
				}
				ke->accept();
				break;
			}

		case Qt::Key_Right:
		case Qt::Key_Left:
			{
				int direction = (ke->key() == Qt::Key_Right ? +1 : -1);
				if (ke->modifiers() == Qt::NoModifier)
				{
					// scroll
					m_leftRightScroll->setValue( m_leftRightScroll->value() +
						direction * cm_scrollAmtHoriz );
				}
				ke->accept();
				break;
			}

		case Qt::Key_Escape:
			cancelDragAction();
			setEditMode(m_lastEditMode);
			break;

		default:
			break;
	}

	// -- The actions below must not be performed during a mouse drag action

	if (m_action != ActionNone)
	{
		update();
		return;
	}

	switch( ke->key() )
	{
		case Qt::Key_Up:
		case Qt::Key_Down:
			{
				int direction = (ke->key() == Qt::Key_Up ? +1 : -1);
				if (ke->modifiers() & Qt::ControlModifier)
				{
					// shift selection up an octave
					// if nothing selected, shift _everything_
					shiftSemiTone(12 * direction);
				}
				else if (ke->modifiers() & Qt::ShiftModifier)
				{
					// Move selected notes up by one semitone
					shiftSemiTone(1 * direction);
				}
				ke->accept();
				break;
			}

		case Qt::Key_Right:
		case Qt::Key_Left:
			{
				int direction = (ke->key() == Qt::Key_Right ? +1 : -1);
				if (ke->modifiers() & Qt::ControlModifier)
				{
					// Move selected notes by one bar to the left
					shiftPos(direction * TimePos::ticksPerBar());
				}
				else if( ke->modifiers() & Qt::ShiftModifier)
				{
					// move notes
					bool quantized = !(ke->modifiers() & Qt::AltModifier);
					int amt = quantized ? quantization() : 1;
					shiftPos(direction * amt);
				}
				else if (ke->modifiers() & Qt::AltModifier)
				{
					// switch to editing a pattern adjacent to this one in the song editor
					Pattern* p = direction > 0
								? m_pattern->nextPattern()
								: m_pattern->previousPattern();
					if (p) { setCurrentPattern(p); }
				}
				ke->accept();
				break;
			}

		case Qt::Key_A:
			if( ke->modifiers() & Qt::ControlModifier )
			{
				ke->accept();
				if (ke->modifiers() & Qt::ShiftModifier)
				{
					// Ctrl + Shift + A = deselect all notes
					clearSelectedNotes();
				}
				else
				{
					// Ctrl + A = select all notes
					selectAll();
				}
				update();
			}
			break;

		case Qt::Key_Escape:
			// On the Knife mode, ESC cancels it
			if (m_editMode == ModeEditKnife)
			{
				setEditMode(m_lastEditMode);
			}
			else
			{
				// Same as Ctrl + Shift + A
				clearSelectedNotes();
			}
			break;

		case Qt::Key_Backspace:
		case Qt::Key_Delete:
			deleteSelectedNotes();
			ke->accept();
			break;

		case Qt::Key_Home:
			m_timeLine->pos().setTicks( 0 );
			m_timeLine->updatePosition();
			ke->accept();
			break;

		case Qt::Key_0:
		case Qt::Key_1:
		case Qt::Key_2:
		case Qt::Key_3:
		case Qt::Key_4:
		case Qt::Key_5:
		case Qt::Key_6:
		case Qt::Key_7:
		case Qt::Key_8:
		case Qt::Key_9:
		{
			int len = 1 + ke->key() - Qt::Key_0;
			if( len == 10 )
			{
				len = 0;
			}
			if( ke->modifiers() & ( Qt::ControlModifier | Qt::KeypadModifier ) )
			{
				m_noteLenModel.setValue( len );
				ke->accept();
			}
			else if( ke->modifiers() & Qt::AltModifier )
			{
				m_quantizeModel.setValue( len );
				ke->accept();
			}
			break;
		}

		case Qt::Key_Control:
			// Ctrl will not enter selection mode if we are
			// in Knife mode, but unquantize it
			if (m_editMode == ModeEditKnife)
			{
				break;
			}
			// Enter selection mode if:
			// -> this window is active
			// -> shift is not pressed
			// (<S-C-drag> is shortcut for sticky note resize)
			if ( !( ke->modifiers() & Qt::ShiftModifier ) && isActiveWindow() )
			{
				setEditMode(ModeSelect);
				ke->accept();
			}
			break;
		default:
			break;
	}

	update();
}




void PianoRoll::keyReleaseEvent(QKeyEvent* ke )
{
	if (!hasValidPattern()) { return; }

	m_ctrlPressed = ke->modifiers() & Qt::ControlModifier;
	m_shiftPressed = ke->modifiers() & Qt::ShiftModifier;
	m_altPressed = ke->modifiers() & Qt::AltModifier;

	if (ke->modifiers() == Qt::NoModifier)
	{
		const int key_num = PianoView::getKeyFromKeyEvent( ke ) + ( DefaultOctave - 1 ) * KeysPerOctave;
		if (!ke->isAutoRepeat() && key_num > -1)
		{
			m_pattern->instrumentTrack()->pianoModel()->handleKeyRelease(key_num);
			// if a chord is set, simulate click release on all chord notes
			pauseChordNotes(key_num);
			ke->accept();
		}
	}

	// -- The actions below must not be performed during a mouse drag action

	if (m_action != ActionNone)
	{
		update();
		return;
	}

	switch( ke->key() )
	{
		case Qt::Key_Control:
			// in knife mode, ctrl disables quantization
			if (m_editMode != ModeEditKnife) { setEditMode(m_lastEditMode); }
			break;

		/* update after undo/redo
		case Qt::Key_Z:
		case Qt::Key_R:
			if (ke->modifiers() == Qt::ControlModifier)	{ update();	}
			break;
		*/
	}

	update();
}




void PianoRoll::leaveEvent(QEvent * e )
{
	QWidget::leaveEvent( e );
	s_textFloat->hide();
	update(); // cleaning inner mouse-related graphics
}




int PianoRoll::noteEditTop() const
{
	return height() - PR_BOTTOM_MARGIN - m_notesEditHeight;
}




int PianoRoll::noteEditBottom() const
{
	return height() - PR_BOTTOM_MARGIN;
}




int PianoRoll::noteEditRight() const
{
	return width() - PR_RIGHT_MARGIN;
}




int PianoRoll::noteEditLeft() const
{
	return m_whiteKeyWidth;
}




int PianoRoll::keyAreaTop() const
{
	return PR_TOP_MARGIN;
}




int PianoRoll::keyAreaBottom() const
{
	return noteEditTop() - NOTE_EDIT_RESIZE_BAR;
}




int PianoRoll::noteAreaWidth() const
{
	return width() - m_whiteKeyWidth - PR_RIGHT_MARGIN;
}




int PianoRoll::noteAreaHeight() const
{
	return keyAreaBottom() - PR_TOP_MARGIN;
}




PianoRoll::PianoRollArea PianoRoll::getPianoRollAreaIn(const int x, const int y)
{
	/* piano editor outline
	 keys     | notes
	 ---------|---------------  <-- note edit area resize bar
	 editmode | noteproperties
	*/
	if (y < keyAreaTop() || y >= noteEditBottom() || x < 0 || x >= noteEditRight())
	{
		return PianoRollArea::Margin;
	}
	else if (y < keyAreaBottom())
	{
		if (x < m_whiteKeyWidth) { return PianoRollArea::Keys; }
		else { return PianoRollArea::Notes; }
	}
	else if (y <= noteEditTop())
	{
		return PianoRollArea::EditAreaResize;
	}
	else // > noteEditTop()
	{
		if (x < m_whiteKeyWidth) { return PianoRollArea::EditMode; }
		else { return PianoRollArea::NoteProperties; }
	}
}

PianoRoll::PianoRollArea PianoRoll::getPianoRollAreaIn()
{
	const QPoint pos = mapFromGlobal(QCursor::pos());
	return getPianoRollAreaIn(pos.x(), pos.y());
}




void PianoRoll::mousePressEvent(QMouseEvent * me)
{
	if (!hasValidPattern()) { return; }

	m_ctrlPressed = me->modifiers() & Qt::ControlModifier;
	m_shiftPressed = me->modifiers() & Qt::ShiftModifier;
	m_altPressed = me->modifiers() & Qt::AltModifier;

	// Ignore button press while another button is being held
	if (m_mouseDownButton != Qt::NoButton) { return; }

	m_startedWithShift = m_shiftPressed;

	const bool leftButton = me->button() == Qt::LeftButton;
	const bool rightButton = me->button() == Qt::RightButton;
	//const bool midButton = me->button() == Qt::MiddleButton;

	// Ignore special mouse buttons
	// At the moment mid button has no use
	if (!(leftButton || rightButton)) { return; }

	const int mey = me->y();
	const int mex = me->x();

	// Area mouse clicked in
	const PianoRollArea pra = getPianoRollAreaIn(mex, mey);

	// save where user clicked
	m_mouseDownButton = me->button();
	m_mouseDownTick = m_hoverTick;
	m_mouseDownKey = m_hoverKey;

	// TODO: make sure this is handled correctly with keyPressEvent
	// if holding control, go to selection mode unless shift is also pressed
	// if (ctrlDown && m_editMode != ModeSelect)
	// {
	// 	m_ctrlMode = m_editMode;
	// 	m_editMode = ModeSelect;
	// 	setCursor(Qt::ArrowCursor);
	// 	update();
	// }

	switch (pra)
	{
		case PianoRollArea::Margin:
		{
			break;
		}
		case PianoRollArea::Keys:
		{
			// reference to last key needed for both
			// right click (used for copy all keys on note)
			// and for playing the key when left-clicked
			//m_lastKey = keyNum;

			if (leftButton)
			{
				int v = MidiDefaultVelocity* mex / m_whiteKeyWidth;
				// side effects of testPlayKey:
				// m_lastKey = keyNum
				// m_lastChord updated
				// calls pauseChordNotes/playChordNotes
				m_action = Actions::ActionPlayKeys;
				testPlayKey(m_hoverKey, v, 0);
			}
			else if (rightButton)
			{
				// right click - tone marker contextual menu
				m_semiToneMarkerMenu->popup(me->globalPos());
			}
			break; // return;
		}
		case PianoRollArea::Notes:
		{
			Note* mouseNote = noteUnderMouse();
			// erase a note, if note != nullptr
			auto tryEraseNote = [=](Note* note) {
				if (note != nullptr)
				{
					m_pattern->addJournalCheckPoint();
					m_pattern->removeNote(note);
					Engine::getSong()->setModified();
				}
			};
			// create a new note, returns m_pattern->addNote
			auto createNewNote = [=](TimePos length, TimePos position, int key) {
				Note newNote(length, position, key);
				newNote.setSelected(true);
				newNote.setPanning(m_lastNotePanning);
				newNote.setVolume(m_lastNoteVolume);
				newNote.setOldKey(key);
				newNote.setOldLength(length);
				newNote.setOldPos(position);
				return m_pattern->addNote(newNote);
			};
			switch (m_editMode)
			{
				case EditModes::ModeEditKnife:
				{
					if (mouseNote && leftButton)
					{
						NoteVector nv {mouseNote};
						m_pattern->splitNotes(nv, TimePos(m_knifeTickPos));
					}
					break;
				}
				case EditModes::ModeEditDetuning:
				{
					if (mouseNote == nullptr) { break; }
					// note this variable is static, saves between function calls
					static QPointer<AutomationPattern> detuningPattern = nullptr;
					if (detuningPattern.data() != nullptr)
					{
						detuningPattern->disconnect(this);
					}
					if (mouseNote->detuning() == nullptr)
					{
						mouseNote->createDetuning();
					}
					detuningPattern = mouseNote->detuning()->automationPattern();
					connect(detuningPattern.data(), SIGNAL(dataChanged()), this, SLOT(update()));
					gui->automationEditor()->open(detuningPattern);
					break;
				}
				case EditModes::ModeDraw:
				{
					// if right click in ModeDraw, erase the note under the mouse (if exists)
					if (rightButton)
					{
						m_action = ActionRemoveNote;
						tryEraseNote(mouseNote);
						break;
					}
					// if we didn't left click, ignore event
					if (!leftButton) { break; }

					// handle left click

					Note* createdNewNote = nullptr;
					// we didn't click on a note, create a new note at mouse position
					if (mouseNote == nullptr)
					{
						m_pattern->addJournalCheckPoint();
						// clear selection and select this new note
						clearSelectedNotes();
						// +32 to quanitize the note correctly when placing notes with
						// the mouse.  We do this here instead of in note.quantized
						// because live notes should still be quantized at the half.
						TimePos notePos(m_hoverTick - (quantization() / 2));
						TimePos noteLen(newNoteLen());

						// create new note and add to pattern
						createdNewNote = createNewNote(noteLen, notePos, m_hoverKey);

						// check for chord draw
						auto cti = InstrumentFunctionNoteStacking::ChordTable::getInstance();
						const auto chord = cti.getChordByName(m_chordModel.currentText());

						// if a chord is selected, create following notes in chord
						// or arpeggio mode
						if (!chord.isEmpty())
						{
							for (int i = 1; i < chord.size(); i++)
							{
								if (m_shiftPressed) // arpeggio mode
								{
									notePos += noteLen;
								}
								Note* note = createNewNote(noteLen, notePos, m_hoverKey + chord[i]);
							}
						}

						m_currentNote = createdNewNote;
						m_lastNotePanning = m_currentNote->getPanning();
						m_lastNoteVolume = m_currentNote->getVolume();
						m_lenOfNewNotes = m_currentNote->length();
					}
					else // select the current note if not selected
					{
						m_currentNote = mouseNote;
						if (!m_currentNote->selected())
						{
							// set note as only selection
							clearSelectedNotes();
							m_currentNote->setSelected(true);
						}
					}

					// Check if m_currentNote is selected
					// If user clicked in an unselected note it won't be
					// if (!m_currentNote->selected())
					// {
					// 	// clear notes and select this note
					// 	clearSelectedNotes();
					// 	m_currentNote->setSelected(true);
					// }

					auto selectedNotes = getSelectedNotes();
					// Reset bounding box for the current selection
					m_moveBoundaryLeft = selectedNotes.first()->pos().getTicks();
					m_moveBoundaryBottom = m_moveBoundaryTop = selectedNotes.first()->key();
					for (Note* note : selectedNotes)
					{
						// save previous position
						note->setOldKey(note->key());
						note->setOldPos(note->pos());
						note->setOldLength(note->length());
						// update boundaries
						m_moveBoundaryBottom = std::min(note->key(), m_moveBoundaryBottom);
						m_moveBoundaryTop = std::max(note->key(), m_moveBoundaryTop);
					}

					// clicked at the "tail" of the note?
					if (mex > xCoordOfTick(m_currentNote->endPos()) - RESIZE_AREA_WIDTH
						&& m_currentNote->length() > 0 )
					{
						m_pattern->addJournalCheckPoint();
						// then resize the note
						m_action = ActionResizeNote;

						//Calculate the minimum length we should allow when resizing
						//each note, and let all notes use the smallest one found
						m_minResizeLen = quantization();
						for (Note *note : selectedNotes)
						{
							//Notes from the BB editor can have a negative length, so
							//change their length to the displayed one before resizing
							if (note->oldLength() <= 0) { note->setOldLength(4); }
							//Let the note be sized down by quantized increments, stopping
							//when the next step down would result in a negative length
							int thisMin = note->oldLength() % quantization();
							//The initial value for m_minResizeLen is the minimum length of
							//a note divisible by the current Q. Therefore we ignore notes
							//where thisMin == 0 when checking for a new minimum
							if (thisMin > 0 && thisMin < m_minResizeLen) { m_minResizeLen = thisMin; }
						}
					}
					else
					{
						if (!createdNewNote)
						{
							m_pattern->addJournalCheckPoint();
						}

						// otherwise move it
						m_action = ActionMoveNote;

						// if they're holding shift, copy all selected notes
						if (!createdNewNote && m_shiftPressed)
						{
							for (Note *note: selectedNotes)
							{
								Note *newNote = m_pattern->addNote(*note, false);
								newNote->setSelected(false);
							}

							if (!selectedNotes.empty())
							{
								// added new notes, so must update engine, song, etc
								Engine::getSong()->setModified();
								update();
								gui->songEditor()->update();
							}
						}

						// Play all notes at the same position as current note
						for (Note* note : selectedNotes)
						{
							if (note->pos() == m_currentNote->pos())
							{
								testPlayNote(note);
							}
						}
					}

					Engine::getSong()->setModified();
					break;
				}
				case EditModes::ModeErase:
				{
					// any mouse button in erase mode erases
					m_action = ActionRemoveNote;
					tryEraseNote(mouseNote);
					break;
				}
				case EditModes::ModeSelect:
				{
					// we start a selection range with left click only
					if (!leftButton) { break; }

					/*
						Note moving in select mode... not a good idea
						Cannot select with ctrl-shift-click

					// if we're over a note
					if (mouseNote)
					{


						// we need to save previous values of selected notes to properly move notes
						auto selectedNotes = getSelectedNotes();
						for (Note* note : selectedNotes)
						{
							note->setOldKey(note->key());
							note->setOldPos(note->pos());
							note->setOldLength(note->length());
						}
						m_action = ActionMoveNote;
						testPlayNote(mouseNote);
					}
					*/

					m_action = ActionSelectNotes;
					return;
				}
			} // switch (m_editMode)
			// DO NOT ADD ANYTHING HERE THANKS
			break;
		}
		case PianoRollArea::NoteProperties:
		{
			m_pattern->addJournalCheckPoint();
			// scribble note edit changes
			m_action = ActionChangeNoteProperty;
			// FIXME: do this without calling mouseMoveEvent
			mouseMoveEvent( me );
			return;
		}
		case PianoRollArea::EditMode:
		{
			if (leftButton)
			{
				// clicked in the box below the keys to the left of note edit area
				m_noteEditMode = static_cast<NoteEditMode>(static_cast<int>(m_noteEditMode)+1);
				if (m_noteEditMode == NoteEditCount)
				{
					m_noteEditMode = static_cast<NoteEditMode>(0);
				}
				// repaint();
			}
			else if (rightButton)
			{
				// pop menu asking which property they want to edit
				m_noteEditMenu->popup(me->globalPos());
			}
			break; // return;
		}
		case PianoRollArea::EditAreaResize:
		{
			m_action = ActionResizeNoteEditArea;
			break; // return;
		}
	}

	update(); // schedule paint event
}




void PianoRoll::mouseDoubleClickEvent(QMouseEvent* me)
{
	if (!hasValidPattern()) { return; }

	const int mey = me->y();
	const int mex = me->x();

	const PianoRollArea pra = getPianoRollAreaIn(mex, mey);

	switch (pra)
	{
		case PianoRollArea::NoteProperties:
		{
			NoteVector nv = getSelectedNotes();

			if (nv.isEmpty() || m_altPressed)
			{
				nv.clear();

				// Find notes closest to pointer
				int pixelRange = 4;
				int minDist = pixelRange * TimePos::ticksPerBar() / m_ppb;
				for (Note* n : m_pattern->notes())
				{
					int dist = std::abs(n->pos() - m_hoverTick);
					if (dist < minDist)
					{
						minDist = dist;
						nv = {n};
					}
					// append all equally close notes on same tick
					else if (dist == minDist && nv.first()->pos() == n->pos())
					{
						nv.append(n);
					}
				}
				if (nv.isEmpty()) { break; }
			}
			enterValue(&nv);
			break;
		}
		default:
		{
			QWidget::mouseDoubleClickEvent(me);
		}
	}
}




void PianoRoll::testPlayNote( Note * n )
{
	if( ! n->isPlaying() && ! m_recording && ! m_stepRecorder.isRecording())
	{
		n->setIsPlaying( true );

		const int baseVelocity = m_pattern->instrumentTrack()->midiPort()->baseVelocity();

		m_pattern->instrumentTrack()->pianoModel()->handleKeyPress(n->key(), n->midiVelocity(baseVelocity));

		MidiEvent event( MidiMetaEvent, -1, n->key(), panningToMidi( n->getPanning() ) );

		event.setMetaEvent( MidiNotePanning );

		m_pattern->instrumentTrack()->processInEvent( event, 0 );
	}
}


void PianoRoll::stopNotes()
{
	for (Note* note : m_pattern->notes())
	{
		if (note->isPlaying())
		{
			m_pattern->instrumentTrack()->pianoModel()->handleKeyRelease(note->key());
			note->setIsPlaying(false);
		}
	}
}

void PianoRoll::playChordNotes(int key, int velocity)
{
	// if a chord is set, play the chords notes beside the base note.
	Piano *pianoModel = m_pattern->instrumentTrack()->pianoModel();
	auto cti = InstrumentFunctionNoteStacking::ChordTable::getInstance();
	m_lastChord = &cti.getChordByName(m_chordModel.currentText());
	if (!m_lastChord->isEmpty())
	{
		for (int i = 1; i < m_lastChord->size(); ++i)
		{
			pianoModel->handleKeyPress(key + (*m_lastChord)[i], velocity);
		}
	}
}

void PianoRoll::pauseChordNotes(int key)
{
	// if a chord was set, stop the chords notes beside the base note.
	Piano *pianoModel = m_pattern->instrumentTrack()->pianoModel();
	if (m_lastChord && !m_lastChord->isEmpty())
	{
		// start at the second key of the chord
		for (int i = 1; i < m_lastChord->size(); ++i)
		{
			pianoModel->handleKeyRelease(key + (*m_lastChord)[i]);
		}
	}
}




void PianoRoll::cancelDragAction()
{
	// Must stop notes before changing their position
	if (m_action == ActionMoveNote)	{ stopNotes(); }

	// Restore dragged notes to their prior state
	if (m_action == ActionMoveNote || m_action == ActionResizeNote)
	{
		for (Note* n : m_pattern->notes())
		{
			if (n->selected())
			{
				n->setPos(n->oldPos());
				n->setKey(n->oldKey());
				n->setLength(n->oldLength());
			}
		}
		update();
	}

	endDragAction();
}




void PianoRoll::endDragAction()
{
	if (m_action == ActionPlayKeys)
	{
		// Stop playing clicked piano key and chord
		m_pattern->instrumentTrack()->pianoModel()->handleKeyRelease(m_lastKey);
		pauseChordNotes(m_lastKey);
	}
	else if (m_action == ActionMoveNote || m_action == ActionChangeNoteProperty)
	{
		// Stop playing notes
		stopNotes();
	}

	s_textFloat->hide();

	m_action = ActionNone;
	m_mouseDownButton = Qt::NoButton;
	m_currentNote = nullptr;
}



void PianoRoll::testPlayKey( int key, int velocity, int pan )
{
	Piano *pianoModel = m_pattern->instrumentTrack()->pianoModel();
	// turn off old key
	pianoModel->handleKeyRelease( m_lastKey );
	// if a chord was set, stop the chords notes as well
	pauseChordNotes(m_lastKey);

	// remember which one we're playing
	m_lastKey = key;

	// play new key
	pianoModel->handleKeyPress( key, velocity );
	// and if a chord is set, play chord notes:
	playChordNotes(key, velocity);
}

void PianoRoll::handleAftertouch(int key, int velocity)
{
	MidiEvent evt(MidiKeyPressure, -1, key, velocity);
	m_pattern->instrumentTrack()->processInEvent(evt);
	if (m_lastChord && !m_lastChord->isEmpty())
	{
		for (int i = 1; i < m_lastChord->size(); ++i)
		{
			evt.setKey(key + (*m_lastChord)[i]);
			m_pattern->instrumentTrack()->processInEvent(evt);
		}
	}
}




void PianoRoll::computeSelectedNotes()
{
	if (!hasValidPattern()) { return; }

	// setup selection-vars
	int posStart = std::min(m_mouseDownTick, m_hoverTick);
	int posEnd = std::max(m_mouseDownTick, m_hoverTick);
	int keyStart = std::min(m_mouseDownKey, m_hoverKey);
	int keyEnd = std::max(m_mouseDownKey, m_hoverKey);

	for( Note *note : m_pattern->notes() )
	{
		// make a new selection unless they're holding shift
		if (!m_shiftPressed) { note->setSelected(false); }

		int noteEnd = note->length() < 0
				? note->pos().getTicks() + 4
				: note->endPos().getTicks();

		// if the selection even barely overlaps the note
		if (note->key() >= keyStart
			&& note->key() <= keyEnd
			&& note->pos() <= posEnd
			&& noteEnd > posStart)
		{
			// remove from selection when holding shift
			bool selected = m_shiftPressed && note->selected();
			note->setSelected( ! selected);
		}
	}

	update();
}




void PianoRoll::mouseReleaseEvent(QMouseEvent* me)
{
	if (!hasValidPattern()) { return; }

	// Ingore release if we haven't regstered a press
	if (me->button() != m_mouseDownButton) { return; }

	// Quit knife mode if we pressed and released the right mouse button
	if (m_editMode == ModeEditKnife && me->button() == Qt::RightButton)
	{
		setEditMode(m_lastEditMode);
	}
	else if (m_action == ActionSelectNotes)
	{
		// select the notes within the selection rectangle
		computeSelectedNotes();
	}
	else if (m_action == ActionMoveNote)
	{
		// we moved one or more notes so they have to be
		// moved properly according to new starting-
		// time in the note-array of pattern
		m_pattern->rearrangeAllNotes();
	}

	if (m_action == ActionMoveNote || m_action == ActionResizeNote)
	{
		// if we only moved one note, deselect it so we can
		// edit the notes in the note edit area
		if (selectionCount() == 1)
		{
			clearSelectedNotes();
		}
	}

	endDragAction();

	repaint();
}




void PianoRoll::mouseMoveEvent(QMouseEvent * me)
{
	// IN GENERAL:
	// Rely on mousePressEvent to set the correct m_action
	// and do not check edit mode or area here

	// if we have no linked pattern return early and schedule paint event
	if (!hasValidPattern()) { return; }
	// TODO why did we update() if no pattern?

	// mouse event x
	const int mex = me->x();
	// mouse event y
	const int mey = me->y();

	// save mouse position
	m_hoverTick = getTick(mex);
	m_hoverKey = getKey(mey);

	switch (m_action)
	{
		case ActionNone:
		{
			// handle cursor updates when the mouse is just moving around normally
			updateCursor();
			break;
		}
		case ActionRemoveNote:
		{
			// check if we have a note under the mouse position and remove it
			 Note* const mouseNote = noteUnderMouse();
			if (mouseNote) { m_pattern->removeNote(mouseNote); }
			break;
		}
		case ActionPlayKeys:
		{
			// Calculate the velocity to play the key
			// TODO: Use std::clamp when we have C++17
			const int v = MidiDefaultVelocity * qBound(0, mex, m_whiteKeyWidth) / m_whiteKeyWidth;

			if (m_hoverKey != m_lastKey)
			{
				// Never play a new key with 0 velocity, as this
				// will be ignored and aftertouch won't work
				testPlayKey(m_hoverKey, std::max(1, v), 0);
			}
			else
			{
				handleAftertouch(m_hoverKey, v);
			}
			break;
		}
		case ActionMoveNote:
		case ActionResizeNote:
		{
			// Handle moving notes and resizing them
			dragNotes();
			break;
		}
		case ActionSelectNotes:
		{
			// Handle horizontal scrolling
			if (mex < noteEditLeft() && m_currentPosition > 0)
			{
				m_hoverTick = m_currentPosition;
				QCursor::setPos(mapToGlobal(QPoint(noteEditLeft(), mey)));
				m_leftRightScroll->setValue(std::max(0, m_currentPosition - 4));
			}
			else if (mex >= noteEditRight())
			{
				m_hoverTick = getTick(noteEditRight() - 1); // -1 to stay inside editor
				QCursor::setPos(mapToGlobal(QPoint(noteEditRight() - 1, mey)));
				m_leftRightScroll->setValue(m_currentPosition + 4);
			}

			// Determine if we need to scroll up/down during select mode
			// because mouse past top/bottom key in current view

			if (mey >= keyAreaBottom())
			{
				QCursor::setPos(mapToGlobal(QPoint(mex, keyAreaBottom() - 1))); // -1  to stay inside editor
				m_topBottomScroll->setValue(m_topBottomScroll->value() + 1);
				m_hoverKey = m_startKey - 1;
			}
			else if (mey < keyAreaTop())
			{
				QCursor::setPos(mapToGlobal(QPoint(mex, keyAreaTop())));
				m_topBottomScroll->setValue(m_topBottomScroll->value() - 1);
				m_hoverKey = getKey(keyAreaTop());
			}
			break;
		}
		case ActionChangeNoteProperty:
		{
			// Do not break if outside NE area, so we can easily create 0% or 200% volume...

			// pixel range for changing notes within mouse x position
			const int pixelRange = 14;
			// ticks within range left of mouse x position
			const int ticksStart = getTick(mex - pixelRange / 2);
			// ticks within range right of the mouse x position
			const int ticksEnd = getTick(mex + pixelRange / 2);

			// Determine what volume/panning to set note to
			// if middle-click, set to defaults

			volume_t vol = DefaultVolume;
			panning_t pan = DefaultPanning;

			// Calculate the value from the mouse position
			if (m_mouseDownButton == Qt::LeftButton)
			{
				// mouse position in note edit area
				const int mouseHeight = noteEditBottom() - mey;
				const int totalHeight = noteEditBottom() - noteEditTop();
				const int volRange = MaxVolume - MinVolume;
				const int panRange = PanningRight - PanningLeft;
				vol = qBound<int>(
					MinVolume,
					MinVolume + volRange * mouseHeight / totalHeight,
					MaxVolume);
				pan = qBound<int>(
					PanningLeft,
					PanningLeft + panRange * mouseHeight / totalHeight,
					PanningRight);
			}

			// Display the value as text
			if (m_noteEditMode == NoteEditVolume)
			{
				m_lastNoteVolume = vol;
				showVolTextFloat(vol, me->pos());
			}
			else if (m_noteEditMode == NoteEditPanning)
			{
				m_lastNotePanning = pan;
				showPanTextFloat(pan, me->pos());
			}

			// Find notes to edit
			const bool hasSelection = isSelection();
			for (Note* n : m_pattern->notes())
			{
				const bool isUnderPosition = n->withinRange(ticksStart, ticksEnd);
				const auto patTrack = m_pattern->instrumentTrack();

				// Play note under the cursor
				if (isUnderPosition && (!hasSelection || n->selected()))
				{
					testPlayNote(n);
				}
				else if (n->isPlaying())
				{
					// Mouse not over this note, stop playing it.
					patTrack->pianoModel()->handleKeyRelease(n->key());
					n->setIsPlaying(false);
				}

				// If note is:
				// Under the cursor, when there is no selection
				// Selected, and alt is not pressed
				// Under the cursor, selected, and alt is pressed
				if ((isUnderPosition && !hasSelection) ||
					(n->selected() && !m_altPressed) ||
					(isUnderPosition && n->selected() && m_altPressed))
				{
					if (m_noteEditMode == NoteEditVolume)
					{
						n->setVolume(vol);
						const int baseVelocity = patTrack->midiPort()->baseVelocity();
						MidiEvent evt(MidiKeyPressure, -1, n->key(), n->midiVelocity(baseVelocity));
						patTrack->processInEvent(evt);
					}
					else if (m_noteEditMode == NoteEditPanning)
					{
						n->setPanning(pan);
						MidiEvent evt(MidiMetaEvent, -1, n->key(), panningToMidi(pan));
						evt.setMetaEvent(MidiNotePanning);
						patTrack->processInEvent(evt);
					}
				}
			}

			// Emit pattern has changed
			emit m_pattern->dataChanged();

			break;
		}
		case ActionResizeNoteEditArea:
		{
			// Center resize bar under mouse
			m_userSetNotesEditHeight = noteEditBottom() - mey - NOTE_EDIT_RESIZE_BAR / 2;
			// Apply bounds and quantization to the new height
			updateNoteEditHeight();
			// Get the corrected height and save it as the one set by user
			m_userSetNotesEditHeight = m_notesEditHeight;
			break;
		}
		default:
		{
			printf("Unhandled PianoRoll::Actions\n");
		}
	}
	update(); // schedule a paint event
}



void PianoRoll::mouseMoveEvent()
{
	// fake mouse move in place
	QMouseEvent me = QMouseEvent(QEvent::MouseMove,
									mapFromGlobal(QCursor::pos()),
									Qt::NoButton,
									m_mouseDownButton,
									QGuiApplication::keyboardModifiers());
	mouseMoveEvent(&me);
}




void PianoRoll::dragNotes()
{
	// dragging one or more notes around

	// convert pixels to ticks and keys
	int off_ticks = m_hoverTick - m_mouseDownTick;
	int off_key = m_hoverKey - m_mouseDownKey;

	// get note-vector of current pattern
	const NoteVector & notes = m_pattern->notes();

	if (m_action == ActionMoveNote)
	{
		// Calculate the offset for either Nudge or Snap modes
		int noteOffset = off_ticks;
		if (m_gridMode == gridSnap && quantization () > 1)
		{
			// Get the mouse timeline absolute position
			TimePos mousePos(m_hoverTick);

			// We create a mousePos that is relative to the end of the note instead
			// of the beginning. That's to see if we will snap the beginning or end
			// of the note
			TimePos mousePosEnd(mousePos);
			mousePosEnd += m_currentNote->oldLength();

			// Now we quantize the mouse position to snap it to the grid
			TimePos mousePosQ = mousePos.quantize(static_cast<float>(quantization()) / DefaultTicksPerBar);
			TimePos mousePosEndQ = mousePosEnd.quantize(static_cast<float>(quantization()) / DefaultTicksPerBar);

			bool snapEnd = abs(mousePosEndQ - mousePosEnd) < abs(mousePosQ - mousePos);

			// Set the offset
			noteOffset = snapEnd
			? mousePosEndQ.getTicks() - m_currentNote->oldPos().getTicks() - m_currentNote->oldLength().getTicks()
			: mousePosQ.getTicks() - m_currentNote->oldPos().getTicks();
		}
		else if (m_gridMode == gridNudge && !m_altPressed)
		{
			// if they're not holding alt, quantize the offset
			noteOffset = off_ticks / quantization() * quantization();
		}

		// Make sure notes won't go outside boundary conditions
		noteOffset = std::max(noteOffset, -m_moveBoundaryLeft);
		// TODO: Use std::clamp when we have C++17
		off_key = qBound(-m_moveBoundaryBottom, off_key, NumKeys - 1 - m_moveBoundaryTop);

		// Apply offset to all selected notes
		for (Note *note : getSelectedNotes())
		{
			// Quick resize is only enabled on Nudge mode, since resizing the note
			// while in Snap mode breaks the calculation of the note offset
			if (m_shiftPressed && ! m_startedWithShift && m_gridMode == gridNudge)
			{
				// quick resize, toggled by holding shift after starting a note move, but not before
				if (note->length() <= 0) { continue; }
				int ticks_new = note->oldLength().getTicks() + noteOffset;
				if( ticks_new <= 0 )
				{
					ticks_new = 1;
				}
				note->setLength( TimePos( ticks_new ) );
				m_lenOfNewNotes = note->length();
			}
			else
			{
				// moving note

				// Final position of the note
				TimePos posTicks(note->oldPos().getTicks() + noteOffset);
				int keyNum = note->oldKey() + off_key;
				int lastKey = note->key();

				note->setPos(posTicks);
				note->setKey(keyNum);

				// note has moved from last key (don't confuse with oldKey, that's the initial key)
				if (note->isPlaying() && lastKey != keyNum)
				{
					// stop the playing note and re-play it with the new key
					m_pattern->instrumentTrack()->pianoModel()->handleKeyRelease(lastKey);
					note->setIsPlaying(false);
					testPlayNote(note);
				}

			}
		}
	}
	else if (m_action == ActionResizeNote)
	{
		// When resizing notes:
		// If shift is not pressed, resize the selected notes but do not rearrange them
		// If shift is pressed we resize and rearrange only the selected notes
		// If shift + ctrl then we also rearrange all posterior notes (sticky)
		// If shift is pressed but only one note is selected, apply sticky

		// Quantize the resizing if alt is not pressed
		if (!m_altPressed)
		{
			off_ticks = floor(off_ticks / quantization()) * quantization();
		}

		auto selectedNotes = getSelectedNotes();

		if (m_shiftPressed)
		{
			// Algorithm:
			// Relative to the starting point of the left-most selected note,
			//   all selected note start-points and *endpoints* (not length) should be scaled by a calculated factor.
			// This factor is such that the endpoint of the note whose handle is being dragged should lie under the cursor.
			// first, determine the start-point of the left-most selected note:
			int stretchStartTick = -1;
			for (const Note *note : selectedNotes)
			{
				if (stretchStartTick < 0 || note->oldPos().getTicks() < stretchStartTick)
				{
					stretchStartTick = note->oldPos().getTicks();
				}
			}
			// determine the ending tick of the right-most selected note
			const Note *posteriorNote = nullptr;
			for (const Note *note : selectedNotes)
			{
				if (posteriorNote == nullptr ||
					note->oldPos().getTicks() + note->oldLength().getTicks() >
					posteriorNote->oldPos().getTicks() + posteriorNote->oldLength().getTicks())
				{
					posteriorNote = note;
				}
			}
			int posteriorEndTick = posteriorNote->pos().getTicks() + posteriorNote->length().getTicks();
			// end-point of the note whose handle is being dragged:
			int stretchEndTick = m_currentNote->oldPos().getTicks() + m_currentNote->oldLength().getTicks();
			// Calculate factor by which to scale the start-point and end-point of all selected notes
			float scaleFactor = (float)(stretchEndTick - stretchStartTick + off_ticks) / qMax(1, stretchEndTick - stretchStartTick);
			scaleFactor = qMax(0.0f, scaleFactor);

			// process all selected notes & determine how much the endpoint of the right-most note was shifted
			int posteriorDeltaThisFrame = 0;
			for (Note *note : selectedNotes)
			{
				// scale relative start and end positions by scaleFactor
				int newStart = stretchStartTick + scaleFactor *
					(note->oldPos().getTicks() - stretchStartTick);
				int newEnd = stretchStartTick + scaleFactor *
					(note->oldPos().getTicks()+note->oldLength().getTicks() - stretchStartTick);
				// if  not holding alt, quantize the offsets
				if (!m_altPressed)
				{
					// quantize start time
					int oldStart = note->oldPos().getTicks();
					int startDiff = newStart - oldStart;
					startDiff = floor(startDiff / quantization()) * quantization();
					newStart = oldStart + startDiff;
					// quantize end time
					int oldEnd = oldStart + note->oldLength().getTicks();
					int endDiff = newEnd - oldEnd;
					endDiff = floor(endDiff / quantization()) * quantization();
					newEnd = oldEnd + endDiff;
				}
				int newLength = qMax(1, newEnd-newStart);
				if (note == posteriorNote)
				{
					posteriorDeltaThisFrame = (newStart+newLength) -
						(note->pos().getTicks() + note->length().getTicks());
				}
				note->setLength( TimePos(newLength) );
				note->setPos( TimePos(newStart) );

				m_lenOfNewNotes = note->length();
			}
			if (m_ctrlPressed || selectionCount() == 1)
			{
				// if holding ctrl or only one note is selected, reposition posterior notes
				for (Note *note : notes)
				{
					if (!note->selected() && note->pos().getTicks() >= posteriorEndTick)
					{
						int newStart = note->pos().getTicks() + posteriorDeltaThisFrame;
						note->setPos( TimePos(newStart) );
					}
				}
			}
		}
		else
		{
			// shift is not pressed; stretch length of selected notes but not their position
			int minLength = m_altPressed ? 1 : m_minResizeLen.getTicks();

			if (m_gridMode == gridSnap)
			{
				// Calculate the end point of the note being dragged
				TimePos oldEndPoint = m_currentNote->oldPos() + m_currentNote->oldLength();
				// Quantize that position
				TimePos quantizedEndPoint = Note::quantized(oldEndPoint, quantization());
				// Add that difference to the offset from the resize
				off_ticks += quantizedEndPoint - oldEndPoint;
			}

			for (Note *note : selectedNotes)
			{
				int newLength = qMax(minLength, note->oldLength() + off_ticks);
				note->setLength(TimePos(newLength));

				m_lenOfNewNotes = note->length();
			}
		}
	}

	m_pattern->updateLength();
	m_pattern->dataChanged();
	Engine::getSong()->setModified();
}




void PianoRoll::paintEvent(QPaintEvent * pe )
{
	bool drawNoteNames = ConfigManager::inst()->value( "ui", "printnotelabels").toInt();

	QStyleOption opt;
	opt.initFrom( this );
	QPainter p( this );
	style()->drawPrimitive( QStyle::PE_Widget, &opt, &p, this );

	QBrush bgColor = p.background();

	// fill with bg color
	p.fillRect( 0, 0, width(), height(), bgColor );

	if (!hasValidPattern())
	{
		QFont f = p.font();
		f.setBold( true );
		p.setFont( pointSize<14>( f ) );
		p.setPen( QApplication::palette().color( QPalette::Active,
							QPalette::BrightText ) );
		p.drawText(m_whiteKeyWidth + 20, PR_TOP_MARGIN + 40,
				tr("Please open a pattern by double-clicking on it!"));
		return;
	}

	// set font-size to 80% of key line height
	QFont f = p.font();
	f.setPixelSize(m_keyLineHeight * 0.8);
	p.setFont(f); // font size doesn't change without this for some reason
	QFontMetrics fontMetrics(p.font());
	// G-1 is one of the widest; plus one pixel margin for the shadow
	QRect const boundingRect = fontMetrics.boundingRect(QString("G-1")) + QMargins(0, 0, 1, 0);

	// Order of drawing
	// - vertical quantization lines
	// - piano roll + horizontal key lines
	// - alternating bar colors
	// - vertical beat lines
	// - vertical bar lines
	// - marked semitones
	// - note editing
	// - notes
	// - selection frame
	// - highlight hovered note
	// - note edit area resize bar
	// - cursor mode icon

	//if (hasValidPattern())
	//{
		// draw vertical quantization lines
		// If we're over 100% zoom, we allow all quantization level grids
		int q = quantization();
		if (m_zoomingModel.value() <= 3)
		{
			// we're under 100% zoom
			// allow quantization grid up to 1/24 for triplets
			if (q % 3 != 0 && q < 8) { q = 8; }
			// allow quantization grid up to 1/32 for normal notes
			else if (q < 6) { q = 6; }
		}
		p.setPen(m_lineColor);
		for (int tick = m_currentPosition - m_currentPosition % q,
			x = xCoordOfTick(tick);
			x <= width();
			tick += q, x = xCoordOfTick(tick))
		{
			p.drawLine(x, keyAreaTop(), x, noteEditBottom());
		}

		// draw horizontal grid lines and piano notes
		p.setClipRect(0, keyAreaTop(), width(), keyAreaBottom() - keyAreaTop());
		// the first grid line from the top Y position
		int grid_line_y = keyAreaTop() + m_keyLineHeight - 1;

		// lambda function for returning the height of a key
		auto keyHeight = [&](
			const int key
		) -> int
		{
			switch (prKeyOrder[key % KeysPerOctave])
			{
			case PR_WHITE_KEY_BIG:
				return m_whiteKeyBigHeight;
			case PR_WHITE_KEY_SMALL:
				return m_whiteKeySmallHeight;
			default:
				return m_blackKeyHeight;
			}
		};
		// lambda function to draw a key
		auto drawKey = [&](
			const int key,
			const int yb)
		{
			const bool mapped = m_pattern->instrumentTrack()->firstKeyModel()->value() <= key &&
				m_pattern->instrumentTrack()->lastKeyModel()->value() >= key;
			const bool pressed = m_pattern->instrumentTrack()->pianoModel()->isKeyPressed(key);

			const int keyCode = key % KeysPerOctave;
			// if the top of the key should align with grid lines
			const bool topAlignedToGrid = Piano::isBlackKey(key) || keyCode == Key_E || keyCode == Key_H;
			const int yt = yb - (topAlignedToGrid ? m_blackKeyHeight : m_whiteKeySmallHeight);
			const int kh = keyHeight(key);
			const int kw = Piano::isBlackKey(key) ? m_blackKeyWidth : m_whiteKeyWidth;
			// set key colors
			p.setPen(QColor(0, 0, 0));
			if (Piano::isWhiteKey(key))
			{
				if (mapped)
				{
					if (pressed) { p.setBrush(m_whiteKeyActiveBackground); }
					else { p.setBrush(m_whiteKeyInactiveBackground); }
				}
				else
				{
					p.setBrush(m_whiteKeyDisabledBackground);
				}
			}
			else
			{
				if (mapped)
				{
					if (pressed) { p.setBrush(m_blackKeyActiveBackground); }
					else { p.setBrush(m_blackKeyInactiveBackground); }
				}
				else
				{
					p.setBrush(m_blackKeyDisabledBackground);
				}
			}
			// draw key
			p.drawRect(PIANO_X, yt, kw, kh);
			// draw note name
			if (keyCode == Key_C || (drawNoteNames && Piano::isWhiteKey(key)))
			{
				// small font sizes have 1 pixel offset instead of 2
				auto zoomOffset = m_zoomYLevels[m_zoomingYModel.value()] > 1.0f ? 2 : 1;
				QString noteString = getNoteString(key);
				QRect textRect(
					m_whiteKeyWidth - boundingRect.width() - 2,
					yb - m_keyLineHeight + zoomOffset,
					boundingRect.width(),
					boundingRect.height()
				);
				p.setPen(pressed ? m_whiteKeyActiveTextShadow : m_whiteKeyInactiveTextShadow);
				p.drawText(textRect.adjusted(0, 1, 1, 0), Qt::AlignRight | Qt::AlignHCenter, noteString);
				p.setPen(pressed ? m_whiteKeyActiveTextColor : m_whiteKeyInactiveTextColor);
				// if (keyCode == Key_C) { p.setPen(textColor()); }
				// else { p.setPen(textColorLight()); }
				p.drawText(textRect, Qt::AlignRight | Qt::AlignHCenter, noteString);
			}
		};
		// lambda for drawing the horizontal grid line
		auto drawHorizontalLine = [&](
			const int key,
			const int y
		)
		{
			if (key % KeysPerOctave == Key_C) { p.setPen(m_beatLineColor); }
			else { p.setPen(m_lineColor); }
			p.drawLine(m_whiteKeyWidth, y, width(), y);
		};

		const int topKey = m_startKey + noteAreaHeight() / m_keyLineHeight - 1;

		// correct y offset of the top key
		if (Piano::isBlackKey(topKey))
		{
			// draw extra white key
			drawKey(topKey + 1, grid_line_y - m_keyLineHeight);
		}
		// loop through visible keys
		for (int key = topKey; key >= m_startKey; --key)
		{
			if (Piano::isWhiteKey(key))
			{
				drawKey(key, grid_line_y);
				drawHorizontalLine(key, grid_line_y);
				grid_line_y += m_keyLineHeight;
			}
			else
			{
				// draw next white key
				drawKey(key - 1, grid_line_y + m_keyLineHeight);
				drawHorizontalLine(key - 1, grid_line_y + m_keyLineHeight);
				// draw black key over previous and next white key
				drawKey(key, grid_line_y);
				drawHorizontalLine(key, grid_line_y);
				// drew two grid keys so skip ahead properly
				grid_line_y += m_keyLineHeight + m_keyLineHeight;
				// capture double key draw
				--key;
			}
		}

		// don't draw over keys
		p.setClipRect(m_whiteKeyWidth, keyAreaTop(), width(), noteEditBottom() - keyAreaTop());

		// draw alternating shading on bars
		float timeSignature =
			static_cast<float>(Engine::getSong()->getTimeSigModel().getNumerator()) /
			static_cast<float>(Engine::getSong()->getTimeSigModel().getDenominator());
		float zoomFactor = m_zoomLevels[m_zoomingModel.value()];
		//the bars which disappears at the left side by scrolling
		int leftBars = m_currentPosition * zoomFactor / TimePos::ticksPerBar();
		//iterates the visible bars and draw the shading on uneven bars
		for (int x = m_whiteKeyWidth, barCount = leftBars;
			x < width() + m_currentPosition * zoomFactor / timeSignature;
			x += m_ppb, ++barCount)
		{
			if ((barCount + leftBars) % 2 != 0)
			{
				p.fillRect(x - m_currentPosition * zoomFactor / timeSignature,
					PR_TOP_MARGIN,
					m_ppb,
					height() - (PR_BOTTOM_MARGIN + PR_TOP_MARGIN),
					m_backgroundShade);
			}
		}

		// draw vertical beat lines
		int ticksPerBeat = DefaultTicksPerBar /
			Engine::getSong()->getTimeSigModel().getDenominator();
		p.setPen(m_beatLineColor);
		for(int tick = m_currentPosition - m_currentPosition % ticksPerBeat,
			x = xCoordOfTick( tick );
			x <= width();
			tick += ticksPerBeat, x = xCoordOfTick(tick))
		{
			p.drawLine(x, PR_TOP_MARGIN, x, noteEditBottom());
		}

		// draw vertical bar lines
		p.setPen(m_barLineColor);
		for(int tick = m_currentPosition - m_currentPosition % TimePos::ticksPerBar(),
			x = xCoordOfTick( tick );
			x <= width();
			tick += TimePos::ticksPerBar(), x = xCoordOfTick(tick))
		{
			p.drawLine(x, PR_TOP_MARGIN, x, noteEditBottom());
		}

		// draw marked semitones after the grid
		for (const int key : m_markedSemiTones)
		{
			// skip if offscreen
			if (key > topKey) { continue; }
			// break after bottom visible key
			if (key < m_startKey) { break; }
			// we're within visible area
			p.fillRect(m_whiteKeyWidth + 1,
				yCoordOfKey(key),
				noteAreaWidth(),
				m_keyLineHeight,
				m_markedSemitoneColor);
		}
	//}

	// reset clip
	p.setClipRect(0, 0, width(), height());

	// erase the area below the piano, because there might be keys that
	// should be only half-visible
	p.fillRect( QRect( 0, keyAreaBottom(),
			m_whiteKeyWidth, noteEditBottom() - keyAreaBottom()), bgColor);

	// display note editing info
	//QFont f = p.font();
	f.setBold( false );
	p.setFont( pointSize<10>( f ) );
	p.setPen(m_noteModeColor);
	p.drawText( QRect( 0, keyAreaBottom(),
					  m_whiteKeyWidth, noteEditBottom() - keyAreaBottom()),
			   Qt::AlignCenter | Qt::TextWordWrap,
			   m_nemStr.at( m_noteEditMode ) + ":" );

	// set clipping area, because we are not allowed to paint over
	// keyboard...
	p.setClipRect(
		m_whiteKeyWidth,
		PR_TOP_MARGIN,
		noteAreaWidth(),
		height() - PR_TOP_MARGIN - PR_BOTTOM_MARGIN);

	// following code draws all notes in visible area
	// and the note editing stuff (volume, panning, etc)

	//if (hasValidPattern())
	//{
		QPolygonF editHandles;

		// -- Begin ghost pattern
		if( !m_ghostNotes.empty() )
		{
			for( const Note *note : m_ghostNotes )
			{
				drawNoteRect(
					p, note, m_ghostNoteColor, m_ghostNoteTextColor, m_selectedNoteColor,
					m_ghostNoteOpacity, m_ghostNoteBorders, drawNoteNames);
			}
		}
		// -- End ghost pattern

		for( const Note *note : m_pattern->notes() )
		{
			drawNoteRect(
					p, note, m_noteColor, m_noteTextColor, m_selectedNoteColor,
					m_noteOpacity, m_noteBorders, drawNoteNames);

			const int x = xCoordOfTick(note->pos());

			// draw note editing stuff
			int editHandleTop = 0;
			if( m_noteEditMode == NoteEditVolume )
			{
				QColor color = m_barColor.lighter(30 + (note->getVolume() * 90 / MaxVolume));
				if( note->selected() )
				{
					color = m_selectedNoteColor;
				}
				p.setPen( QPen( color, NOTE_EDIT_LINE_WIDTH ) );

				editHandleTop = noteEditBottom() -
						(m_notesEditHeight * (note->getVolume() - MinVolume) / (MaxVolume - MinVolume));

				p.drawLine(QLine (x, editHandleTop, x, noteEditBottom()));

			}
			else if( m_noteEditMode == NoteEditPanning )
			{
				QColor color = note->selected() ? m_selectedNoteColor : m_noteColor;
				p.setPen( QPen( color, NOTE_EDIT_LINE_WIDTH ) );

				editHandleTop = noteEditBottom() -
						((m_notesEditHeight * (note->getPanning() - PanningLeft)) / (PanningRight - PanningLeft));

				p.drawLine(QLine(x, noteEditTop() + (m_notesEditHeight / 2), x, editHandleTop));
			}
			editHandles << QPoint (x, editHandleTop);

			if( note->hasDetuningInfo() )
			{
				drawDetuningInfo(p, note, x, yCoordOfKey(note->key()));
				p.setClipRect(
					m_whiteKeyWidth,
					PR_TOP_MARGIN,
					noteAreaWidth(),
					height() - PR_TOP_MARGIN);
			}
		}

		// -- Knife tool (draw cut line)
		if (m_editMode == ModeEditKnife && m_knifeTickPos > 0)
		{
			const int x = xCoordOfTick(m_knifeTickPos);
			const int y = yCoordOfKey(m_hoverKey) - 1;  // start drawing on grid line above

			p.setPen(QPen(m_knifeCutLineColor, 1));
			p.drawLine(x, y, x, y + m_keyLineHeight);
		}

		//draw current step recording notes
		for( const Note *note : m_stepRecorder.getCurStepNotes() )
		{
			drawNoteRect(
				p, note, m_stepRecorder.curStepNoteColor(), m_noteTextColor, m_selectedNoteColor,
				m_noteOpacity, m_noteBorders, drawNoteNames);
		}

		p.setPen(QPen(m_noteColor, NOTE_EDIT_LINE_WIDTH + 2));
		p.drawPoints( editHandles );

	//}

	p.setClipRect(
		m_whiteKeyWidth,
		PR_TOP_MARGIN,
		noteAreaWidth(),
		noteAreaHeight());

	// now draw selection-frame
	if (m_action == ActionSelectNotes)
	{
		// +1 tick and -1 key (keys count backwards) makes the selection end at the start of the next tick/key
		// y is also offset by -1 px to align to the grid lines
		const int x = xCoordOfTick(std::min(m_mouseDownTick, m_hoverTick));
		const int y = yCoordOfKey(std::max(m_mouseDownKey, m_hoverKey)) - 1;
		const int w = xCoordOfTick(std::max(m_mouseDownTick, m_hoverTick) + 1) - x;
		const int h = yCoordOfKey(std::min(m_mouseDownKey, m_hoverKey) - 1) - y - 1;

		p.setPen(m_selectedNoteColor);
		p.setBrush( Qt::NoBrush );
		p.drawRect(x, y, w, h);
	}

	// TODO: Get this out of paint event
	int l = ( hasValidPattern() )? (int) m_pattern->length() : 0;

	// reset scroll-range
	if( m_leftRightScroll->maximum() != l )
	{
		m_leftRightScroll->setRange( 0, l );
		m_leftRightScroll->setPageStep( l );
	}

	// set line colors
	QColor editAreaCol = QColor(m_lineColor);
	QColor currentKeyCol = QColor(m_beatLineColor);

	editAreaCol.setAlpha( 64 );
	currentKeyCol.setAlpha( 64 );

	// bar to resize note edit area
	p.setClipRect( 0, 0, width(), height() );
	p.fillRect( QRect( 0, keyAreaBottom(),
					width()-PR_RIGHT_MARGIN, NOTE_EDIT_RESIZE_BAR ), editAreaCol );

	// if mouse is inside note area
	if (getPianoRollAreaIn() == PianoRollArea::Notes)
	{
		// horizontal line for the key under the cursor
		p.fillRect(m_whiteKeyWidth, yCoordOfKey(m_hoverKey) + 3,
					noteAreaWidth(), m_keyLineHeight - 7,
					currentKeyCol);

		const QPixmap * cursor = NULL;
		switch (m_action)
		{
			case ActionRemoveNote: cursor = s_toolErase; break;
			case ActionMoveNote: cursor = s_toolMove; break;
			case ActionSelectNotes: cursor = s_toolSelect; break;
			case ActionResizeNote: cursor = s_toolDraw; break;
			case ActionPlayKeys: cursor = nullptr; break;
			default: switch (m_editMode)
			{
				case ModeDraw: cursor = s_toolDraw; break;
				case ModeErase: cursor = s_toolErase; break;
				case ModeSelect: cursor = s_toolSelect; break;
				case ModeEditDetuning: cursor = s_toolOpen; break;
				case ModeEditKnife: cursor = s_toolKnife; break;
			}
		}
		// draw current edit-mode-icon below the cursor
		if (cursor)
		{
			p.drawPixmap(mapFromGlobal(QCursor::pos()) + QPoint(8, 8), *cursor);
		}
	}
}




void PianoRoll::updateScrollbars()
{
	m_leftRightScroll->setGeometry(
		m_whiteKeyWidth,
		height() - SCROLLBAR_SIZE,
		noteAreaWidth(),
		SCROLLBAR_SIZE
	);
	m_topBottomScroll->setGeometry(
		width() - SCROLLBAR_SIZE,
		keyAreaTop(),
		SCROLLBAR_SIZE,
		height() - keyAreaTop() - SCROLLBAR_SIZE
	);
	int pianoAreaHeight = keyAreaBottom() - keyAreaTop();
	int numKeysVisible = pianoAreaHeight / m_keyLineHeight;
	m_totalKeysToScroll = qMax(0, NumKeys - numKeysVisible);
	m_topBottomScroll->setRange(0, m_totalKeysToScroll);
	if (m_startKey > m_totalKeysToScroll)
	{
		m_startKey = qMax(0, m_totalKeysToScroll);
	}
	m_topBottomScroll->setValue(m_totalKeysToScroll - m_startKey);
}

// responsible for moving/resizing scrollbars after window-resizing
void PianoRoll::resizeEvent(QResizeEvent* re)
{
	updateNoteEditHeight();  // handles scrollbars etc
	Engine::getSong()->getPlayPos(Song::Mode_PlayPattern)
		.m_timeLine->setFixedWidth(width());
	update();
}



void PianoRoll::updateNoteEditHeight()
{
	// both areas, margins excluded
	int both = noteAreaHeight() + noteEditBottom() - noteEditTop();

	// calculate all heights so the key area always is quantized to the hight of a piano key
	int userDefined = both - ((both - m_userSetNotesEditHeight) / m_keyLineHeight * m_keyLineHeight);
	int noteEditMin = both - ((both - NOTE_EDIT_MIN_HEIGHT) / m_keyLineHeight * m_keyLineHeight);
	int keyAreaMin = KEY_AREA_MIN_HEIGHT / m_keyLineHeight * m_keyLineHeight;
	int keyAreaMax = NumKeys * m_keyLineHeight;

	// height will be clamped in this order of priority:
	// 1. no bigger if key area is min
	// 2. no smaller if key area is max
	// 3. no smaller than note edit min
	m_notesEditHeight = std::min(std::max(std::max(userDefined, noteEditMin), both - keyAreaMax), both - keyAreaMin);

	// Update all widgets that depend on note edit height
	updateScrollbars();
	updatePositionLineHeight();
	m_stepRecorderWidget.setBottomMargin(keyAreaBottom());
}



void PianoRoll::wheelEvent(QWheelEvent * we )
{
	we->accept();

	// handle wheel events for note edit area - for editing note vol/pan with mousewheel
	if (getPianoRollAreaIn() == PianoRollArea::NoteProperties)
	{
		if (!hasValidPattern()) {return;}
		// get values for going through notes
		int pixel_range = 8;
		int x = position(we).x();
		int ticks_start = getTick(x - pixel_range / 2);
		int ticks_end = getTick(x + pixel_range / 2);

		const bool hasSelection = isSelection();
		// go through notes to figure out which one we want to change
		NoteVector nv;
		for (Note* n: m_pattern->notes())
		{
			const bool isUnderPosition = n->withinRange(ticks_start, ticks_end);
			// If note is:
			// Under the cursor, when there is no selection
			// Selected, and alt is not pressed
			// Under the cursor, selected, and alt is pressed
			if ((isUnderPosition && !hasSelection)
				|| (n->selected() && !m_altPressed)
				|| (isUnderPosition && n->selected() && m_altPressed))
			{
				nv += n;
			}
		}
		if( nv.size() > 0 )
		{
			const int step = we->angleDelta().y() > 0 ? 1 : -1;
			if( m_noteEditMode == NoteEditVolume )
			{
				for ( Note * n : nv )
				{
					volume_t vol = qBound<int>( MinVolume, n->getVolume() + step, MaxVolume );
					n->setVolume( vol );
				}
				bool allVolumesEqual = std::all_of( nv.begin(), nv.end(),
					[nv](const Note *note)
					{
						return note->getVolume() == nv[0]->getVolume();
					});
				if ( allVolumesEqual )
				{
					// show the volume hover-text only if all notes have the
					// same volume
					showVolTextFloat(nv[0]->getVolume(), position(we), 1000);
				}
			}
			else if( m_noteEditMode == NoteEditPanning )
			{
				for ( Note * n : nv )
				{
					panning_t pan = qBound<int>( PanningLeft, n->getPanning() + step, PanningRight );
					n->setPanning( pan );
				}
				bool allPansEqual = std::all_of( nv.begin(), nv.end(),
					[nv](const Note *note)
					{
						return note->getPanning() == nv[0]->getPanning();
					});
				if ( allPansEqual )
				{
					// show the pan hover-text only if all notes have the same
					// panning
					showPanTextFloat( nv[0]->getPanning(), position( we ), 1000 );
				}
			}
			update();
		}
	}

	// not in note edit area, so handle scrolling/zooming and quantization change
	else
	if( we->modifiers() & Qt::ControlModifier && we->modifiers() & Qt::AltModifier )
	{
		int q = m_quantizeModel.value();
		if((we->angleDelta().x() + we->angleDelta().y()) > 0) // alt + scroll becomes horizontal scroll on KDE
		{
			q--;
		}
		else if((we->angleDelta().x() + we->angleDelta().y()) < 0) // alt + scroll becomes horizontal scroll on KDE
		{
			q++;
		}
		q = qBound( 0, q, m_quantizeModel.size() - 1 );
		m_quantizeModel.setValue( q );
	}
	else if( we->modifiers() & Qt::ControlModifier && we->modifiers() & Qt::ShiftModifier )
	{
		int l = m_noteLenModel.value();
		if(we->angleDelta().y() > 0)
		{
			l--;
		}
		else if(we->angleDelta().y() < 0)
		{
			l++;
		}
		l = qBound( 0, l, m_noteLenModel.size() - 1 );
		m_noteLenModel.setValue( l );
	}
	else if( we->modifiers() & Qt::ControlModifier )
	{
		int z = m_zoomingModel.value();
		if(we->angleDelta().y() > 0)
		{
			z++;
		}
		else if(we->angleDelta().y() < 0)
		{
			z--;
		}
		z = qBound( 0, z, m_zoomingModel.size() - 1 );

		int x = (position(we).x() - m_whiteKeyWidth) * TimePos::ticksPerBar();
		// ticks based on the mouse x-position where the scroll wheel was used
		int ticks = x / m_ppb;
		// what would be the ticks in the new zoom level on the very same mouse x
		int newTicks = x / (DEFAULT_PR_PPB * m_zoomLevels[z]);
		// scroll so the tick "selected" by the mouse x doesn't move on the screen
		m_leftRightScroll->setValue(m_leftRightScroll->value() + ticks - newTicks);
		// update combobox with zooming-factor
		m_zoomingModel.setValue( z );
	}

	// FIXME: Reconsider if determining orientation is necessary in Qt6.
	else if(abs(we->angleDelta().x()) > abs(we->angleDelta().y())) // scrolling is horizontal
	{
		m_leftRightScroll->setValue(m_leftRightScroll->value() -
							we->angleDelta().x() * 2 / 15);
	}
	else if(we->modifiers() & Qt::ShiftModifier)
	{
		m_leftRightScroll->setValue(m_leftRightScroll->value() -
							we->angleDelta().y() * 2 / 15);
	}
	else
	{
		m_topBottomScroll->setValue(m_topBottomScroll->value() -
							we->angleDelta().y() / 30);
	}
}




void PianoRoll::focusOutEvent( QFocusEvent * )
{
	if (!hasValidPattern()) { return; }

	m_ctrlPressed = m_shiftPressed = m_altPressed = false;

	// Silence everything
	for (int key=0; key < NumKeys; key++)
	{
		m_pattern->instrumentTrack()->pianoModel()->handleKeyRelease(key);
	}

	cancelDragAction();
	setEditMode(m_lastEditMode);
}

void PianoRoll::focusInEvent( QFocusEvent * ev )
{
	if ( hasValidPattern() )
	{
		// Assign midi device
		m_pattern->instrumentTrack()->autoAssignMidiDevice(true);
	}
	QWidget::focusInEvent(ev);
}




int PianoRoll::getTick(int x) const
{
	return (x - m_whiteKeyWidth) * TimePos::ticksPerBar() / m_ppb + m_currentPosition;
}




int PianoRoll::getKey(int y) const
{
	int key_num = qBound(
		0,
		// Since keyAreaBottom is not part of the editor we must start from pixel *above*
		// Also make sure value is positive before int division with m_keyLineHeight
		// otherwise both the pixels above and below bottom line rounds to 0
		((keyAreaBottom() - 1 - y + m_startKey * m_keyLineHeight) / m_keyLineHeight) ,
		NumKeys - 1
	);
	return key_num;
}




int PianoRoll::xCoordOfTick(int tick) const
{
	return ((tick - m_currentPosition) * m_ppb / TimePos::ticksPerBar()) + m_whiteKeyWidth;
}




int PianoRoll::yCoordOfKey(int key) const
{
	return keyAreaBottom() - ((key - m_startKey) * m_keyLineHeight) - m_keyLineHeight;
}




QList<int> PianoRoll::getAllOctavesForKey( int keyToMirror ) const
{
	QList<int> keys;

	for (int i=keyToMirror % KeysPerOctave; i < NumKeys; i += KeysPerOctave)
	{
		keys.append(i);
	}

	return keys;
}

Song::PlayModes PianoRoll::desiredPlayModeForAccompany() const
{
	if( m_pattern->getTrack()->trackContainer() ==
					Engine::getBBTrackContainer() )
	{
		return Song::Mode_PlayBB;
	}
	return Song::Mode_PlaySong;
}




void PianoRoll::play()
{
	if( ! hasValidPattern() )
	{
		return;
	}

	if( Engine::getSong()->playMode() != Song::Mode_PlayPattern )
	{
		Engine::getSong()->playPattern( m_pattern );
	}
	else
	{
		Engine::getSong()->togglePause();
	}
}




void PianoRoll::record()
{
	if( Engine::getSong()->isPlaying() )
	{
		stop();
	}
	if( m_recording || ! hasValidPattern() )
	{
		return;
	}

	m_pattern->addJournalCheckPoint();
	m_recording = true;

	Engine::getSong()->playPattern( m_pattern, false );
}




void PianoRoll::recordAccompany()
{
	if( Engine::getSong()->isPlaying() )
	{
		stop();
	}
	if( m_recording || ! hasValidPattern() )
	{
		return;
	}

	m_pattern->addJournalCheckPoint();
	m_recording = true;

	if( m_pattern->getTrack()->trackContainer() == Engine::getSong() )
	{
		Engine::getSong()->playSong();
	}
	else
	{
		Engine::getSong()->playBB();
	}
}




bool PianoRoll::toggleStepRecording()
{
	if(m_stepRecorder.isRecording())
	{
		m_stepRecorder.stop();
	}
	else
	{
		if(hasValidPattern())
		{
			if(Engine::getSong()->isPlaying())
			{
				m_stepRecorder.start(0, newNoteLen());
			}
			else
			{
				m_stepRecorder.start(
					Engine::getSong()->getPlayPos(
						Song::Mode_PlayPattern), newNoteLen());
			}
		}
	}

	return m_stepRecorder.isRecording();;
}




void PianoRoll::stop()
{
	Engine::getSong()->stop();
	m_recording = false;
	m_scrollBack = ( m_timeLine->autoScroll() == TimeLineWidget::AutoScrollEnabled );
}




void PianoRoll::startRecordNote(const Note & n )
{
	if(hasValidPattern())
	{
		if( m_recording &&
			Engine::getSong()->isPlaying() &&
			(Engine::getSong()->playMode() == desiredPlayModeForAccompany() ||
			Engine::getSong()->playMode() == Song::Mode_PlayPattern ))
		{
			TimePos sub;
			if( Engine::getSong()->playMode() == Song::Mode_PlaySong )
			{
				sub = m_pattern->startPosition();
			}
			Note n1( 1, Engine::getSong()->getPlayPos(
						Engine::getSong()->playMode() ) - sub,
					n.key(), n.getVolume(), n.getPanning() );
			if( n1.pos() >= 0 )
			{
				m_recordingNotes << n1;
			}
		}
		else if (m_stepRecorder.isRecording())
		{
			m_stepRecorder.notePressed(n);
		}
	}
}




void PianoRoll::finishRecordNote(const Note & n )
{
	if(hasValidPattern())
	{
		if( m_recording &&
			Engine::getSong()->isPlaying() &&
				( Engine::getSong()->playMode() ==
						desiredPlayModeForAccompany() ||
					Engine::getSong()->playMode() ==
						Song::Mode_PlayPattern ) )
		{
			for( QList<Note>::Iterator it = m_recordingNotes.begin();
						it != m_recordingNotes.end(); ++it )
			{
				if( it->key() == n.key() )
				{
					Note n1( n.length(), it->pos(),
							it->key(), it->getVolume(),
							it->getPanning() );
					n1.quantizeLength( quantization() );
					m_pattern->addNote( n1 );
					update();
					m_recordingNotes.erase( it );
					break;
				}
			}
		}
		else if (m_stepRecorder.isRecording())
		{
			m_stepRecorder.noteReleased(n);
		}
	}
}




void PianoRoll::horScrolled(int new_pos )
{
	m_currentPosition = new_pos;
	m_stepRecorderWidget.setCurrentPosition(m_currentPosition);
	emit positionChanged( m_currentPosition );

	mouseMoveEvent();
	update();
}




void PianoRoll::verScrolled( int new_pos )
{
	// revert value
	m_startKey = qMax(0, m_totalKeysToScroll - new_pos);

	mouseMoveEvent();
	update();
}




void PianoRoll::setEditMode(int mode)
{
	m_editMode = static_cast<EditModes>(mode);

	// Knife and holding ctrl are temporary modes, do not remember them
	if (m_editMode != ModeEditKnife && !m_ctrlPressed)
	{
		m_lastEditMode = m_editMode;
	}
	updateCursor();
	update();
}




void PianoRoll::selectAll()
{
	if (hasValidPattern())
	{
		for(Note *note: m_pattern->notes())
		{
			note->setSelected(true);
		}
	}
}




// returns vector with pointers to all selected notes
NoteVector PianoRoll::getSelectedNotes() const
{
	NoteVector selectedNotes;

	if (hasValidPattern())
	{
		for( Note *note : m_pattern->notes() )
		{
			if( note->selected() )
			{
				selectedNotes.push_back( note );
			}
		}
	}
	return selectedNotes;
}

// selects all notess associated with m_lastKey
void PianoRoll::selectNotesOnKey()
{
	if (hasValidPattern()) {
		for (Note * note : m_pattern->notes()) {
			if (note->key() == m_lastKey) {
				note->setSelected(true);
			}
		}
	}
}

void PianoRoll::enterValue( NoteVector* nv )
{

	if( m_noteEditMode == NoteEditVolume )
	{
		bool ok;
		int new_val;
		new_val = QInputDialog::getInt(	this, "Piano roll: note velocity",
					tr( "Please enter a new value between %1 and %2:" ).
						arg( MinVolume ).arg( MaxVolume ),
					(*nv)[0]->getVolume(),
					MinVolume, MaxVolume, 1, &ok );

		if( ok )
		{
			for ( Note * n : *nv )
			{
				n->setVolume( new_val );
			}
			m_lastNoteVolume = new_val;
		}
	}
	else if( m_noteEditMode == NoteEditPanning )
	{
		bool ok;
		int new_val;
		new_val = QInputDialog::getInt(	this, "Piano roll: note panning",
					tr( "Please enter a new value between %1 and %2:" ).
							arg( PanningLeft ).arg( PanningRight ),
						(*nv)[0]->getPanning(),
						PanningLeft, PanningRight, 1, &ok );

		if( ok )
		{
			for ( Note * n : *nv )
			{
				n->setPanning( new_val );
			}
			m_lastNotePanning = new_val;
		}

	}
}



void PianoRoll::copyToClipboard( const NoteVector & notes ) const
{
	// For copyString() and MimeType enum class
	using namespace Clipboard;

	DataFile dataFile( DataFile::ClipboardData );
	QDomElement note_list = dataFile.createElement( "note-list" );
	dataFile.content().appendChild( note_list );

	TimePos start_pos( notes.front()->pos().getBar(), 0 );
	for( const Note *note : notes )
	{
		Note clip_note( *note );
		clip_note.setPos( clip_note.pos( start_pos ) );
		clip_note.saveState( dataFile, note_list );
	}

	copyString( dataFile.toString(), MimeType::Default );
}




void PianoRoll::copySelectedNotes()
{
	NoteVector selected_notes = getSelectedNotes();

	if( ! selected_notes.empty() )
	{
		copyToClipboard( selected_notes );
	}
}




void PianoRoll::cutSelectedNotes()
{
	if( ! hasValidPattern() )
	{
		return;
	}

	NoteVector selected_notes = getSelectedNotes();

	if( ! selected_notes.empty() )
	{
		m_pattern->addJournalCheckPoint();

		copyToClipboard( selected_notes );

		Engine::getSong()->setModified();

		for( Note *note : selected_notes )
		{
			// note (the memory of it) is also deleted by
			// pattern::removeNote(...) so we don't have to do that
			m_pattern->removeNote( note );
		}
	}

	update();
	gui->songEditor()->update();
}




void PianoRoll::pasteNotes()
{
	// For getString() and MimeType enum class
	using namespace Clipboard;

	if( ! hasValidPattern() )
	{
		return;
	}

	QString value = getString( MimeType::Default );

	if( ! value.isEmpty() )
	{
		DataFile dataFile( value.toUtf8() );

		QDomNodeList list = dataFile.elementsByTagName( Note::classNodeName() );

		// remove selection and select the newly pasted notes
		clearSelectedNotes();

		if( ! list.isEmpty() )
		{
			m_pattern->addJournalCheckPoint();
		}

		for( int i = 0; ! list.item( i ).isNull(); ++i )
		{
			// create the note
			Note cur_note;
			cur_note.restoreState( list.item( i ).toElement() );
			cur_note.setPos( cur_note.pos() + Note::quantized( m_timeLine->pos(), quantization() ) );

			// select it
			cur_note.setSelected( true );

			// add to pattern
			m_pattern->addNote( cur_note, false );
		}

		// we only have to do the following lines if we pasted at
		// least one note...
		Engine::getSong()->setModified();
		update();
		gui->songEditor()->update();
	}
}




//Return false if no notes are deleted
bool PianoRoll::deleteSelectedNotes()
{
	if (!hasValidPattern()) { return false; }

	auto selectedNotes = getSelectedNotes();
	if (selectedNotes.empty()) { return false; }

	m_pattern->addJournalCheckPoint();

	for (Note* note: selectedNotes) { m_pattern->removeNote( note ); }

	Engine::getSong()->setModified();
	update();
	gui->songEditor()->update();
	return true;
}




void PianoRoll::autoScroll( const TimePos & t )
{
	const int w = noteAreaWidth();
	if( t > m_currentPosition + w * TimePos::ticksPerBar() / m_ppb )
	{
		m_leftRightScroll->setValue( t.getBar() * TimePos::ticksPerBar() );
	}
	else if( t < m_currentPosition )
	{
		TimePos t2 = qMax( t - w * TimePos::ticksPerBar() *
					TimePos::ticksPerBar() / m_ppb, (tick_t) 0 );
		m_leftRightScroll->setValue( t2.getBar() * TimePos::ticksPerBar() );
	}
	m_scrollBack = false;
}




void PianoRoll::updatePosition( const TimePos & t )
{
	if( ( Engine::getSong()->isPlaying()
			&& Engine::getSong()->playMode() == Song::Mode_PlayPattern
			&& m_timeLine->autoScroll() == TimeLineWidget::AutoScrollEnabled
		) || m_scrollBack )
	{
		autoScroll( t );
	}
	// ticks relative to m_currentPosition
	// < 0 = outside viewport left
	// > width = outside viewport right
	const int pos = (static_cast<int>(m_timeLine->pos()) - m_currentPosition) * m_ppb / TimePos::ticksPerBar();
	// if pos is within visible range, show it
	if (pos >= 0 && pos <= width() - m_whiteKeyWidth)
	{
		m_positionLine->show();
		// adjust pos for piano keys width and self line width (align to rightmost of line)
		m_positionLine->move(pos + m_whiteKeyWidth - (m_positionLine->width() - 1), keyAreaTop());
	}
	else
	{
		m_positionLine->hide();
	}
}


void PianoRoll::updatePositionLineHeight()
{
	m_positionLine->setFixedHeight(keyAreaBottom() - keyAreaTop());
}




void PianoRoll::updatePositionAccompany( const TimePos & t )
{
	Song * s = Engine::getSong();

	if( m_recording && hasValidPattern() &&
					s->playMode() != Song::Mode_PlayPattern )
	{
		TimePos pos = t;
		if( s->playMode() != Song::Mode_PlayBB )
		{
			pos -= m_pattern->startPosition();
		}
		if( (int) pos > 0 )
		{
			s->getPlayPos( Song::Mode_PlayPattern ).setTicks( pos );
			autoScroll( pos );
		}
	}
}


void PianoRoll::updatePositionStepRecording( const TimePos & t )
{
	if( m_stepRecorder.isRecording() )
	{
		autoScroll( t );
	}
}


void PianoRoll::zoomingChanged()
{
	m_ppb = m_zoomLevels[m_zoomingModel.value()] * DEFAULT_PR_PPB;

	assert( m_ppb > 0 );

	m_timeLine->setPixelsPerBar( m_ppb );
	m_stepRecorderWidget.setPixelsPerBar( m_ppb );
	m_positionLine->zoomChange(m_zoomLevels[m_zoomingModel.value()]);

	update();
}


void PianoRoll::zoomingYChanged()
{
	m_keyLineHeight = m_zoomYLevels[m_zoomingYModel.value()] * DEFAULT_KEY_LINE_HEIGHT;
	m_whiteKeySmallHeight = qFloor(m_keyLineHeight * 1.5);
	m_whiteKeyBigHeight = m_keyLineHeight * 2;
	m_blackKeyHeight = m_keyLineHeight; //round(m_keyLineHeight * 1.3333);

	updateNoteEditHeight(); // handles scrollbars etc
	update();
}


void PianoRoll::quantizeChanged()
{
	update();
}

void PianoRoll::noteLengthChanged()
{
	m_stepRecorder.setStepsLength(newNoteLen());
	update();
}

void PianoRoll::keyChanged()
{
	markSemiTone(stmaMarkCurrentScale, false);
}

int PianoRoll::quantization() const
{
	if( m_quantizeModel.value() == 0 )
	{
		if( m_noteLenModel.value() > 0 )
		{
			return newNoteLen();
		}
		else
		{
			return DefaultTicksPerBar / 16;
		}
	}

	return DefaultTicksPerBar / Quantizations[m_quantizeModel.value() - 1];
}


void PianoRoll::quantizeNotes(QuantizeActions mode)
{
	if( ! hasValidPattern() )
	{
		return;
	}

	m_pattern->addJournalCheckPoint();

	NoteVector notes = getSelectedNotes();

	if( notes.empty() )
	{
		for( Note* n : m_pattern->notes() )
		{
			notes.push_back( n );
		}
	}

	for( Note* n : notes )
	{
		if( n->length() == TimePos( 0 ) )
		{
			continue;
		}

		Note copy(*n);
		m_pattern->removeNote( n );
		if (mode == QuantizeBoth || mode == QuantizePos)
		{
			copy.quantizePos(quantization());
		}
		if (mode == QuantizeBoth || mode == QuantizeLength)
		{
			copy.quantizeLength(quantization());
		}
		m_pattern->addNote(copy, false);
	}

	update();
	gui->songEditor()->update();
	Engine::getSong()->setModified();
}




void PianoRoll::updateSemiToneMarkerMenu()
{
	auto cti = InstrumentFunctionNoteStacking::ChordTable::getInstance();
	auto scale = cti.getScaleByName(m_scaleModel.currentText());
	auto chord = cti.getChordByName(m_chordModel.currentText());

	emit semiToneMarkerMenuScaleSetEnabled( ! scale.isEmpty() );
	emit semiToneMarkerMenuChordSetEnabled( ! chord.isEmpty() );
}




TimePos PianoRoll::newNoteLen() const
{
	if( m_noteLenModel.value() == 0 )
	{
		return m_lenOfNewNotes;
	}

	QString text = m_noteLenModel.currentText();
	return DefaultTicksPerBar / text.right( text.length() - 2 ).toInt();
}




bool PianoRoll::mouseOverNote()
{
	return hasValidPattern() && noteUnderMouse() != NULL;
}




Note * PianoRoll::noteUnderMouse()
{
	// make sure we are inside note area
	if (getPianoRollAreaIn() != PianoRollArea::Notes) { return nullptr; }

	// loop through whole note-vector...
	for( Note* const& note : m_pattern->notes() )
	{
		int noteEnd = note->length() < 0
					? note->pos().getTicks() + 4
					: note->endPos().getTicks();

		// and check whether the cursor is over an
		// existing note
		if( m_hoverTick >= note->pos()
				&& m_hoverTick <= noteEnd
				&& note->key() == m_hoverKey
				&& note->length() != 0 )
		{
			return note;
		}
	}

	return nullptr;
}




void PianoRoll::updateCursor()
{
	// If we are resizing the edit area, use SizeVerCursor
	QPoint pos = mapFromGlobal(QCursor::pos());

	if (getPianoRollAreaIn(pos.x(), pos.y()) == PianoRollArea::EditAreaResize)
	{
		setCursor(Qt::SizeVerCursor);
		return;
	}

	// Check if we have a note under the mouse position, nullptr if not
	Note* const mouseNote = noteUnderMouse();

	if (m_editMode == ModeDraw && mouseNote)
	{
		// If we are over a note use SizeAllCursor unless we are
		// at the tail of the note, then we use SizeHorCursor
		const int noteTailX = xCoordOfTick(mouseNote->endPos());
		const bool atTail =	mouseNote->length() > 0	&& pos.x() > noteTailX - RESIZE_AREA_WIDTH;

		setCursor(atTail ? Qt::SizeHorCursor : Qt::SizeAllCursor);
		return;
	}
	else if (m_editMode == ModeEditKnife && mouseNote)
	{
		// Set position of cut line
		// - if ctrl is pressed, do not quantize it
		// - else round to the *closest* grid line (instead of rounding down)
		m_knifeTickPos = m_ctrlPressed
						? m_hoverTick
						: (m_hoverTick + quantization() / 2) / quantization() * quantization();
		// Hide the cursor
		setCursor(Qt::BlankCursor);
		return;
	}

	// Default is Arrow Cursor and no knife cut line
	setCursor(Qt::ArrowCursor);
	m_knifeTickPos = 0;
}




void PianoRoll::changeSnapMode()
{
	//	gridNudge,
	//	gridSnap,
	//	gridFree - to be implemented

	m_gridMode = static_cast<GridMode>(m_snapModel.value());
}

PianoRollWindow::PianoRollWindow() :
	Editor(true, true),
	m_editor(new PianoRoll())
{
	setCentralWidget( m_editor );

	m_playAction->setToolTip(tr( "Play/pause current pattern (Space)" ) );
	m_recordAction->setToolTip(tr( "Record notes from MIDI-device/channel-piano" ) );
	m_recordAccompanyAction->setToolTip( tr( "Record notes from MIDI-device/channel-piano while playing song or BB track" ) );
	m_toggleStepRecordingAction->setToolTip( tr( "Record notes from MIDI-device/channel-piano, one step at the time" ) );
	m_stopAction->setToolTip( tr( "Stop playing of current pattern (Space)" ) );

	DropToolBar *notesActionsToolBar = addDropToolBarToTop( tr( "Edit actions" ) );

	// init edit-buttons at the top
	ActionGroup* editModeGroup = new ActionGroup( this );
	QAction* drawAction = editModeGroup->addAction( embed::getIconPixmap( "edit_draw" ), tr( "Draw mode (Shift+D)" ) );
	QAction* eraseAction = editModeGroup->addAction( embed::getIconPixmap( "edit_erase" ), tr("Erase mode (Shift+E)" ) );
	QAction* selectAction = editModeGroup->addAction( embed::getIconPixmap( "edit_select" ), tr( "Select mode (Shift+S)" ) );
	QAction* pitchBendAction = editModeGroup->addAction( embed::getIconPixmap( "automation" ), tr("Pitch Bend mode (Shift+T)" ) );

	drawAction->setChecked( true );

	drawAction->setShortcut( Qt::SHIFT | Qt::Key_D );
	eraseAction->setShortcut( Qt::SHIFT | Qt::Key_E );
	selectAction->setShortcut( Qt::SHIFT | Qt::Key_S );
	pitchBendAction->setShortcut( Qt::SHIFT | Qt::Key_T );

	connect( editModeGroup, SIGNAL( triggered( int ) ), m_editor, SLOT( setEditMode( int ) ) );

	// Quantize combo button
	QToolButton* quantizeButton = new QToolButton(notesActionsToolBar);
	QMenu* quantizeButtonMenu = new QMenu(quantizeButton);

	QAction* quantizeAction = new QAction(embed::getIconPixmap("quantize"), tr("Quantize"), this);
	QAction* quantizePosAction = new QAction(tr("Quantize positions"), this);
	QAction* quantizeLengthAction = new QAction(tr("Quantize lengths"), this);

	connect(quantizeAction, &QAction::triggered, [this](){ m_editor->quantizeNotes(); });
	connect(quantizePosAction, &QAction::triggered, [this](){ m_editor->quantizeNotes(PianoRoll::QuantizePos); });
	connect(quantizeLengthAction, &QAction::triggered, [this](){ m_editor->quantizeNotes(PianoRoll::QuantizeLength); });

	quantizeButton->setPopupMode(QToolButton::MenuButtonPopup);
	quantizeButton->setDefaultAction(quantizeAction);
	quantizeButton->setMenu(quantizeButtonMenu);
	quantizeButtonMenu->addAction(quantizePosAction);
	quantizeButtonMenu->addAction(quantizeLengthAction);

	notesActionsToolBar->addAction( drawAction );
	notesActionsToolBar->addAction( eraseAction );
	notesActionsToolBar->addAction( selectAction );
	notesActionsToolBar->addAction( pitchBendAction );
	notesActionsToolBar->addSeparator();
	notesActionsToolBar->addWidget(quantizeButton);

	// -- File actions
	DropToolBar* fileActionsToolBar = addDropToolBarToTop(tr("File actions"));

	// -- File ToolButton
	m_fileToolsButton = new QToolButton(m_toolBar);
	m_fileToolsButton->setIcon(embed::getIconPixmap("file"));
	m_fileToolsButton->setPopupMode(QToolButton::InstantPopup);

	// Import / export
	QAction* importAction = new QAction(embed::getIconPixmap("project_import"),
		tr("Import pattern"), m_fileToolsButton);

	QAction* exportAction = new QAction(embed::getIconPixmap("project_export"),
		tr("Export pattern"), m_fileToolsButton);

	m_fileToolsButton->addAction(importAction);
	m_fileToolsButton->addAction(exportAction);
	fileActionsToolBar->addWidget(m_fileToolsButton);

	connect(importAction, SIGNAL(triggered()), this, SLOT(importPattern()));
	connect(exportAction, SIGNAL(triggered()), this, SLOT(exportPattern()));
	// -- End File actions

	// Copy + paste actions
	DropToolBar *copyPasteActionsToolBar =  addDropToolBarToTop( tr( "Copy paste controls" ) );

	QAction* cutAction = new QAction(embed::getIconPixmap( "edit_cut" ),
								tr( "Cut (%1+X)" ).arg(UI_CTRL_KEY), this );

	QAction* copyAction = new QAction(embed::getIconPixmap( "edit_copy" ),
								 tr( "Copy (%1+C)" ).arg(UI_CTRL_KEY), this );

	QAction* pasteAction = new QAction(embed::getIconPixmap( "edit_paste" ),
					tr( "Paste (%1+V)" ).arg(UI_CTRL_KEY), this );

	cutAction->setShortcut( Qt::CTRL | Qt::Key_X );
	copyAction->setShortcut( Qt::CTRL | Qt::Key_C );
	pasteAction->setShortcut( Qt::CTRL | Qt::Key_V );

	connect( cutAction, SIGNAL( triggered() ), m_editor, SLOT( cutSelectedNotes() ) );
	connect( copyAction, SIGNAL( triggered() ), m_editor, SLOT( copySelectedNotes() ) );
	connect( pasteAction, SIGNAL( triggered() ), m_editor, SLOT( pasteNotes() ) );

	copyPasteActionsToolBar->addAction( cutAction );
	copyPasteActionsToolBar->addAction( copyAction );
	copyPasteActionsToolBar->addAction( pasteAction );


	DropToolBar *timeLineToolBar = addDropToolBarToTop( tr( "Timeline controls" ) );
	m_editor->m_timeLine->addToolButtons( timeLineToolBar );

	// -- Note modifier tools
	QToolButton * noteToolsButton = new QToolButton(m_toolBar);
	noteToolsButton->setIcon(embed::getIconPixmap("tool"));
	noteToolsButton->setPopupMode(QToolButton::InstantPopup);

	QAction * glueAction = new QAction(embed::getIconPixmap("glue"),
				tr("Glue"), noteToolsButton);
	connect(glueAction, SIGNAL(triggered()), m_editor, SLOT(glueNotes()));
	glueAction->setShortcut( Qt::SHIFT | Qt::Key_G );

	QAction * knifeAction = new QAction(embed::getIconPixmap("edit_knife"),
				tr("Knife"), noteToolsButton);
	connect(knifeAction, &QAction::triggered, m_editor, [this](){ m_editor->setEditMode(PianoRoll::ModeEditKnife); });
	knifeAction->setShortcut( Qt::SHIFT | Qt::Key_K );

	QAction* fillAction = new QAction(embed::getIconPixmap("fill"), tr("Fill"), noteToolsButton);
	connect(fillAction, &QAction::triggered, [this](){ m_editor->fitNoteLengths(true); });
	fillAction->setShortcut(Qt::SHIFT | Qt::Key_F);

	QAction* cutOverlapsAction = new QAction(embed::getIconPixmap("cut_overlaps"), tr("Cut overlaps"), noteToolsButton);
	connect(cutOverlapsAction, &QAction::triggered, [this](){ m_editor->fitNoteLengths(false); });
	cutOverlapsAction->setShortcut(Qt::SHIFT | Qt::Key_C);

	QAction* minLengthAction = new QAction(embed::getIconPixmap("min_length"), tr("Min length as last"), noteToolsButton);
	connect(minLengthAction, &QAction::triggered, [this](){ m_editor->constrainNoteLengths(false); });

	QAction* maxLengthAction = new QAction(embed::getIconPixmap("max_length"), tr("Max length as last"), noteToolsButton);
	connect(maxLengthAction, &QAction::triggered, [this](){ m_editor->constrainNoteLengths(true); });

	noteToolsButton->addAction(glueAction);
	noteToolsButton->addAction(knifeAction);
	noteToolsButton->addAction(fillAction);
	noteToolsButton->addAction(cutOverlapsAction);
	noteToolsButton->addAction(minLengthAction);
	noteToolsButton->addAction(maxLengthAction);

	notesActionsToolBar->addWidget(noteToolsButton);

	addToolBarBreak();


	DropToolBar *zoomAndNotesToolBar = addDropToolBarToTop( tr( "Zoom and note controls" ) );

	QLabel * zoom_lbl = new QLabel( m_toolBar );
	zoom_lbl->setPixmap( embed::getIconPixmap( "zoom_x" ) );

	m_zoomingComboBox = new ComboBox( m_toolBar );
	m_zoomingComboBox->setModel( &m_editor->m_zoomingModel );
	m_zoomingComboBox->setFixedSize( 64, ComboBox::DEFAULT_HEIGHT );
	m_zoomingComboBox->setToolTip( tr( "Horizontal zooming") );

	QLabel * zoom_y_lbl = new QLabel(m_toolBar);
	zoom_y_lbl->setPixmap(embed::getIconPixmap("zoom_y"));

	m_zoomingYComboBox = new ComboBox(m_toolBar);
	m_zoomingYComboBox->setModel(&m_editor->m_zoomingYModel);
	m_zoomingYComboBox->setFixedSize(64, ComboBox::DEFAULT_HEIGHT);
	m_zoomingYComboBox->setToolTip(tr("Vertical zooming"));

	// setup quantize-stuff
	QLabel * quantize_lbl = new QLabel( m_toolBar );
	quantize_lbl->setPixmap( embed::getIconPixmap( "quantize" ) );

	m_quantizeComboBox = new ComboBox( m_toolBar );
	m_quantizeComboBox->setModel( &m_editor->m_quantizeModel );
	m_quantizeComboBox->setFixedSize( 64, ComboBox::DEFAULT_HEIGHT );
	m_quantizeComboBox->setToolTip( tr( "Quantization") );

	// setup note-len-stuff
	QLabel * note_len_lbl = new QLabel( m_toolBar );
	note_len_lbl->setPixmap( embed::getIconPixmap( "note" ) );

	m_noteLenComboBox = new ComboBox( m_toolBar );
	m_noteLenComboBox->setModel( &m_editor->m_noteLenModel );
	m_noteLenComboBox->setFixedSize( 105, ComboBox::DEFAULT_HEIGHT );
	m_noteLenComboBox->setToolTip( tr( "Note length") );

	// setup key-stuff
	m_keyComboBox = new ComboBox(m_toolBar);
	m_keyComboBox->setModel(&m_editor->m_keyModel);
	m_keyComboBox->setFixedSize(72, ComboBox::DEFAULT_HEIGHT);
	m_keyComboBox->setToolTip(tr("Key"));

	// setup scale-stuff
	QLabel * scale_lbl = new QLabel( m_toolBar );
	scale_lbl->setPixmap( embed::getIconPixmap( "scale" ) );

	m_scaleComboBox = new ComboBox( m_toolBar );
	m_scaleComboBox->setModel( &m_editor->m_scaleModel );
	m_scaleComboBox->setFixedSize( 105, ComboBox::DEFAULT_HEIGHT );
	m_scaleComboBox->setToolTip( tr( "Scale") );

	// setup chord-stuff
	QLabel * chord_lbl = new QLabel( m_toolBar );
	chord_lbl->setPixmap( embed::getIconPixmap( "chord" ) );

	m_chordComboBox = new ComboBox( m_toolBar );
	m_chordComboBox->setModel( &m_editor->m_chordModel );
	m_chordComboBox->setFixedSize( 105, ComboBox::DEFAULT_HEIGHT );
	m_chordComboBox->setToolTip( tr( "Chord" ) );

	// setup snap-stuff
	QLabel* snapLbl = new QLabel(m_toolBar);
	snapLbl->setPixmap(embed::getIconPixmap("gridmode"));

	m_snapComboBox = new ComboBox(m_toolBar);
	m_snapComboBox->setModel(&m_editor->m_snapModel);
	m_snapComboBox->setFixedSize(105, ComboBox::DEFAULT_HEIGHT);
	m_snapComboBox->setToolTip(tr("Snap mode"));

	// -- Clear ghost pattern button
	m_clearGhostButton = new QPushButton( m_toolBar );
	m_clearGhostButton->setIcon( embed::getIconPixmap( "clear_ghost_note" ) );
	m_clearGhostButton->setToolTip( tr( "Clear ghost notes" ) );
	m_clearGhostButton->setEnabled( false );
	connect( m_clearGhostButton, SIGNAL( clicked() ), m_editor, SLOT( clearGhostPattern() ) );
	connect( m_editor, SIGNAL( ghostPatternSet( bool ) ), this, SLOT( ghostPatternSet( bool ) ) );

	// Wrap label icons and comboboxes in a single widget so when
	// the window is resized smaller in width it hides both
	QWidget * zoom_widget = new QWidget();
	QHBoxLayout * zoom_hbox = new QHBoxLayout();
	zoom_hbox->setContentsMargins(0, 0, 0, 0);
	zoom_hbox->addWidget(zoom_lbl);
	zoom_hbox->addWidget(m_zoomingComboBox);
	zoom_widget->setLayout(zoom_hbox);
	zoomAndNotesToolBar->addWidget(zoom_widget);

	QWidget * zoomY_widget = new QWidget();
	QHBoxLayout * zoomY_hbox = new QHBoxLayout();
	zoomY_hbox->setContentsMargins(0, 0, 0, 0);
	zoomY_hbox->addWidget(zoom_y_lbl);
	zoomY_hbox->addWidget(m_zoomingYComboBox);
	zoomY_widget->setLayout(zoomY_hbox);
	zoomAndNotesToolBar->addWidget(zoomY_widget);

	QWidget * quantize_widget = new QWidget();
	QHBoxLayout * quantize_hbox = new QHBoxLayout();
	quantize_hbox->setContentsMargins(0, 0, 0, 0);
	quantize_hbox->addWidget(quantize_lbl);
	quantize_hbox->addWidget(m_quantizeComboBox);
	quantize_widget->setLayout(quantize_hbox);
	zoomAndNotesToolBar->addSeparator();
	zoomAndNotesToolBar->addWidget(quantize_widget);

	QWidget * note_widget = new QWidget();
	QHBoxLayout * note_hbox = new QHBoxLayout();
	note_hbox->setContentsMargins(0, 0, 0, 0);
	note_hbox->addWidget(note_len_lbl);
	note_hbox->addWidget(m_noteLenComboBox);
	note_widget->setLayout(note_hbox);
	zoomAndNotesToolBar->addSeparator();
	zoomAndNotesToolBar->addWidget(note_widget);

	QWidget * scale_widget = new QWidget();
	QHBoxLayout * scale_hbox = new QHBoxLayout();
	scale_hbox->setContentsMargins(0, 0, 0, 0);
	scale_hbox->addWidget(scale_lbl);
	// Add the key selection between scale label and key
	scale_hbox->addWidget(m_keyComboBox);
	scale_hbox->addWidget(m_scaleComboBox);
	scale_widget->setLayout(scale_hbox);
	zoomAndNotesToolBar->addSeparator();
	zoomAndNotesToolBar->addWidget(scale_widget);

	QWidget * chord_widget = new QWidget();
	QHBoxLayout * chord_hbox = new QHBoxLayout();
	chord_hbox->setContentsMargins(0, 0, 0, 0);
	chord_hbox->addWidget(chord_lbl);
	chord_hbox->addWidget(m_chordComboBox);
	chord_widget->setLayout(chord_hbox);
	zoomAndNotesToolBar->addSeparator();
	zoomAndNotesToolBar->addWidget(chord_widget);

	zoomAndNotesToolBar->addSeparator();
	zoomAndNotesToolBar->addWidget( m_clearGhostButton );

	QWidget* snapWidget = new QWidget();
	QHBoxLayout* snapHbox = new QHBoxLayout();
	snapHbox->setContentsMargins(0, 0, 0, 0);
	snapHbox->addWidget(snapLbl);
	snapHbox->addWidget(m_snapComboBox);
	snapWidget->setLayout(snapHbox);
	zoomAndNotesToolBar->addSeparator();
	zoomAndNotesToolBar->addWidget(snapWidget);

	// setup our actual window
	setFocusPolicy( Qt::StrongFocus );
	setFocus();
	setWindowIcon( embed::getIconPixmap( "piano" ) );
	setCurrentPattern( NULL );

	// Connections
	connect( m_editor, SIGNAL( currentPatternChanged() ), this, SIGNAL( currentPatternChanged() ) );
	connect( m_editor, SIGNAL( currentPatternChanged() ), this, SLOT( updateAfterPatternChange() ) );
}




const Pattern* PianoRollWindow::currentPattern() const
{
	return m_editor->currentPattern();
}




void PianoRollWindow::setGhostPattern( Pattern* pattern )
{
	m_editor->setGhostPattern( pattern );
}




void PianoRollWindow::setCurrentPattern( Pattern* pattern )
{
	m_editor->setCurrentPattern( pattern );

	if ( pattern )
	{
		setWindowTitle( tr( "Piano-Roll - %1" ).arg( pattern->name() ) );
		m_fileToolsButton->setEnabled(true);
		connect( pattern->instrumentTrack(), SIGNAL( nameChanged() ), this, SLOT( updateAfterPatternChange()) );
		connect( pattern, SIGNAL( dataChanged() ), this, SLOT( updateAfterPatternChange() ) );
	}
	else
	{
		setWindowTitle( tr( "Piano-Roll - no pattern" ) );
		m_fileToolsButton->setEnabled(false);
	}
}




bool PianoRollWindow::isRecording() const
{
	return m_editor->isRecording();
}




int PianoRollWindow::quantization() const
{
	return m_editor->quantization();
}




void PianoRollWindow::play()
{
	m_editor->play();
}




void PianoRollWindow::stop()
{
	m_editor->stop();
}




void PianoRollWindow::record()
{
	stopStepRecording(); //step recording mode is mutually exclusive with other record modes

	m_editor->record();
}




void PianoRollWindow::recordAccompany()
{
	stopStepRecording(); //step recording mode is mutually exclusive with other record modes

	m_editor->recordAccompany();
}


void PianoRollWindow::toggleStepRecording()
{
	if(isRecording())
	{
		// step recording mode is mutually exclusive with other record modes
		// stop them before starting step recording
		stop();
	}

	m_editor->toggleStepRecording();

	updateStepRecordingIcon();
}

void PianoRollWindow::stopRecording()
{
	m_editor->stopRecording();
}




void PianoRollWindow::reset()
{
	m_editor->reset();
}




void PianoRollWindow::saveSettings( QDomDocument & doc, QDomElement & de )
{
	if( !m_editor->ghostNotes().empty() )
	{
		QDomElement ghostNotesRoot = doc.createElement( "ghostnotes" );
		for( Note *note : m_editor->ghostNotes() )
		{
			QDomElement ghostNoteNode = doc.createElement( "ghostnote" );
			ghostNoteNode.setAttribute( "len", note->length() );
			ghostNoteNode.setAttribute( "key", note->key() );
			ghostNoteNode.setAttribute( "pos", note->pos() );

			ghostNotesRoot.appendChild(ghostNoteNode);
		}
		de.appendChild( ghostNotesRoot );
	}

	if (m_editor->m_markedSemiTones.length() > 0)
	{
		QDomElement markedSemiTonesRoot = doc.createElement("markedSemiTones");
		for (int ix = 0; ix < m_editor->m_markedSemiTones.size(); ++ix)
		{
			QDomElement semiToneNode = doc.createElement("semiTone");
			semiToneNode.setAttribute("key", m_editor->m_markedSemiTones.at(ix));
			markedSemiTonesRoot.appendChild(semiToneNode);
		}
		de.appendChild(markedSemiTonesRoot);
	}

	MainWindow::saveWidgetState( this, de );
}




void PianoRollWindow::loadSettings( const QDomElement & de )
{
	m_editor->loadGhostNotes( de.firstChildElement("ghostnotes") );
	m_editor->loadMarkedSemiTones(de.firstChildElement("markedSemiTones"));

	MainWindow::restoreWidgetState( this, de );

	// update margins here because we're later in the startup process
	// We can't earlier because everything is still starting with the
	// WHITE_KEY_WIDTH default
	QMargins qm = m_editor->m_stepRecorderWidget.margins();
	qm.setLeft(m_editor->m_whiteKeyWidth);
	m_editor->m_stepRecorderWidget.setMargins(qm);
	m_editor->m_timeLine->setXOffset(m_editor->m_whiteKeyWidth);
}




QSize PianoRollWindow::sizeHint() const
{
	return { INITIAL_PIANOROLL_WIDTH, INITIAL_PIANOROLL_HEIGHT };
}



bool PianoRollWindow::hasFocus() const
{
	return m_editor->hasFocus();
}



void PianoRollWindow::updateAfterPatternChange()
{
	patternRenamed();
	updateStepRecordingIcon(); //pattern change turn step recording OFF - update icon accordingly
}

void PianoRollWindow::patternRenamed()
{
	if ( currentPattern() )
	{
		setWindowTitle( tr( "Piano-Roll - %1" ).arg( currentPattern()->name() ) );
		m_fileToolsButton->setEnabled(true);
	}
	else
	{
		setWindowTitle( tr( "Piano-Roll - no pattern" ) );
		m_fileToolsButton->setEnabled(false);
	}
}




void PianoRollWindow::ghostPatternSet( bool state )
{
	m_clearGhostButton->setEnabled( state );
}




void PianoRollWindow::exportPattern()
{
	FileDialog exportDialog(this, tr("Export pattern"), "",
		tr("XML pattern file (*.xpt *.xptz)"));

	exportDialog.setAcceptMode(FileDialog::AcceptSave);

	if (exportDialog.exec() == QDialog::Accepted &&
		!exportDialog.selectedFiles().isEmpty() &&
		!exportDialog.selectedFiles().first().isEmpty())
	{
		QString suffix =
			ConfigManager::inst()->value("app", "nommpz").toInt() == 0
				? "xptz"
				: "xpt";
		exportDialog.setDefaultSuffix(suffix);

		const QString fullPath = exportDialog.selectedFiles()[0];
		DataFile dataFile(DataFile::NotePattern);
		m_editor->m_pattern->saveSettings(dataFile, dataFile.content());

		if (dataFile.writeFile(fullPath))
		{
			TextFloat::displayMessage(tr("Export pattern success"),
				tr("Pattern saved to %1").arg(fullPath),
				embed::getIconPixmap("project_export"), 4000);
		}
	}
}




void PianoRollWindow::importPattern()
{
	// Overwrite confirmation.
	if (!m_editor->m_pattern->empty() &&
		QMessageBox::warning(
			NULL,
			tr("Import pattern."),
			tr("You are about to import a pattern, this will "
				"overwrite your current pattern. Do you want to "
				"continue?"),
			QMessageBox::Yes | QMessageBox::No, QMessageBox::Yes
		) != QMessageBox::Yes)
	{
		return;
	}

	FileDialog importDialog(this, tr("Open pattern"), "",
		tr("XML pattern file (*.xpt *.xptz)"));
	importDialog.setFileMode(FileDialog::ExistingFile);

	if (importDialog.exec() == QDialog::Accepted &&
		!importDialog.selectedFiles().isEmpty())
	{
		const QString fullPath = importDialog.selectedFiles()[0];
		DataFile dataFile(fullPath);

		if (dataFile.head().isNull())
		{
			return;
		}

		TimePos pos = m_editor->m_pattern->startPosition(); // Backup position in timeline.

		m_editor->m_pattern->loadSettings(dataFile.content());
		m_editor->m_pattern->movePosition(pos);

		TextFloat::displayMessage(tr("Import pattern success"),
			tr("Imported pattern %1!").arg(fullPath),
			embed::getIconPixmap("project_import"), 4000);
	}
}




void PianoRollWindow::focusInEvent( QFocusEvent * event )
{
	// when the window is given focus, also give focus to the actual piano roll
	m_editor->setFocus( event->reason() );
}

void PianoRollWindow::stopStepRecording()
{
	if(m_editor->isStepRecording())
	{
		m_editor->toggleStepRecording();
		updateStepRecordingIcon();
	}
}

void PianoRollWindow::updateStepRecordingIcon()
{
	if(m_editor->isStepRecording())
	{
		m_toggleStepRecordingAction->setIcon(embed::getIconPixmap("record_step_on"));
	}
	else
	{
		m_toggleStepRecordingAction->setIcon(embed::getIconPixmap("record_step_off"));
	}
}
