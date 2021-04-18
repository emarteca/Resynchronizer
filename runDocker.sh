#!/bin/bash

mkdir local_mount
docker run --mount type=bind,source=`pwd`/local_mount,destination=/mount -w /home/resynchronizer -it \
			--user=0 \
		    --env="DISPLAY" \
		    --env="QT_X11_NO_MITSHM=1" \
		    --volume="/tmp/.X11-unix:/tmp/.X11-unix:rw" \
		    resynchronizer:latest 
		    
rm -r local_mount
