#ifndef _HYDROGEN_IMPORT_H
#define _HYDROGEN_IMPORT_H

#include <QString>

#include "core/ImportFilter.h"


class HydrogenImport : public ImportFilter
{
public:
	HydrogenImport( const QString & _file );
        bool readSong();

	virtual ~HydrogenImport();

	virtual PluginView * instantiateView( QWidget * )
	{
		return( nullptr );
	}
private:
	virtual bool tryImport( TrackContainer* tc );
};
#endif

