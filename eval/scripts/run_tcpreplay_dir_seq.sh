#/bin/bash
################################################################################
# Bash script for replaying multiple pcaps sequentially: for Meta4 IoT
#  - Description: 
#  - Author: Hyojoon Kim (joonk@princeton.edu)
################################################################################

################################################################################
# Copyright (C) 2021  Hyojoon Kim (Princeton University)
#
# This program is free software: you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation, either version 3 of the License, or (at your option) any later
# version.
# 
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License along
# with this program.  If not, see <http://www.gnu.org/licenses/>.
################################################################################


DIR=${1%/}
INTF=$2
TIMEOUT_SECOND=$3

# Check arguments
if [ -z $DIR ]
then
    echo "No directory supplied (1st argument)"
    exit 1
fi

if [ -z $INTF ]
then
    echo "No interface supplied (2nd argument)"
    exit 1
fi

cd $DIR
PCAPS='capture.pcap147'

for i in $(seq 148 158)
do  
  echo $PCAPS
  sudo tcpreplay -i $INTF $PCAPS
  PCAPS='capture.pcap'$i
done

