#!/bin/sh  
#============ get the file name ===========  
Folder_A="../sv_comp/array-examples"   
Output_file="sv_comp2_2.txt"  
#这里用于清空原本的输出文件，感觉 : 这个符号用处挺大，shell的学习还是要多用才是  
: > $Output_file         
                                                                                                                                   
for file_a in ${Folder_A}/*; do  
    temp_file=`basename $file_a`  
    # echo $temp_file >>	$Output_file  
    ./arrayAnalysis ${Folder_A}/$temp_file -- >> $Output_file  
done  


