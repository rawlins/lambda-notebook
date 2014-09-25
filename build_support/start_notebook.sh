#!/bin/sh
cd `/usr/bin/dirname $0`
WD=`pwd`
/usr/bin/osascript -e "tell application \"Terminal\" to do script \"$WD/start_notebook\""
