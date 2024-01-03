
json_tree <- function(training_data,i){
  
  # out1223 = paste0(",{\"attribute\":\"",tree_struc_info[node_id,]$var , "\",\"cut\":0,\"classification\":true,\"children\":[")
  
  tree = Building_tree(training_data,i)

  #plotted_tree =   rpart.plot(tree,type=4,compress = FALSE,
  #                            extra=101,
  #                            box.palette="GnBu",
  #                            branch.lty=3, 
  #                            shadow.col="gray", 
  #                            nn=TRUE)
  
  plotted_tree= rpart.plot(tree,type=4,compress = FALSE,
             extra=101,
             box.palette="GnBu",
             branch.lty=3, 
             shadow.col="gray", 
             nn=TRUE)
  
  #Storing information about tree
  tree_struc_info = get_frame_with_parent(tree)
  tree_struc = struc_data_frame(tree_struc_info)
  
  #selecting internal nodes
  int_node_list = subset(tree_struc,child1!='null')
  int_node_list = subset(int_node_list,child2!='null')
  row.names(tree_struc_info)<- tree_struc_info$nodeid
  row.names(tree_struc)<- tree_struc$nodeid
  
  dfs_list = depthFirstValues(tree_struc)
  
  out = paste0('{\"attribute\":\"$func\",\"cut\":',i,',\"classification\":true,\"children\":[')
  
  nodes_covered = list()
  IS_FIRST = TRUE
  for(i in 1:length(dfs_list)){
    nodes_covered[length(nodes_covered)+1] = dfs_list[i]
    child_idx =""
    is_right = FALSE
    if(length(which(dfs_list[i] %in% tree_struc$child2)) > 0)  is_right = TRUE
    curr_node = as.integer(row.names(tree_struc_info %>% subset(node_id==as.integer(dfs_list[i]))))
    if(tree_struc_info[curr_node,]$var != '<leaf>'){
      attr = tree_struc_info[curr_node,]$var
      child1 = tree_struc[which(tree_struc$nodeid == tree_struc_info[curr_node,]$node_id),]$child1
      child2 = tree_struc[which(tree_struc$nodeid == tree_struc_info[curr_node,]$node_id),]$child2
      if(child1 != "null"){
        child_idx =  child1
      }
      if(child_idx =="" && child2 != "null"){
        child_idx = child2
      }
      cut = strsplit(tree_struc_info[which(tree_struc_info$node_id == child_idx),]$node_label, '[>,<,=]')[[1]][length(strsplit(tree_struc_info[which(tree_struc_info$node_id == child_idx),]$node_label, split = '[>,<,=]')[[1]])] 
      
      #cut = ceiling(as.numeric(cut))
            
      classification = strsplit(plotted_tree$labs[as.integer( row.names(tree_struc_info %>% subset(node_id == as.integer(dfs_list[i]))))], "\\n")[[1]][1] 
      #print(paste0('[{\"attribute\":\"',attr , '\",\"cut\":',cut,',\"classification\":',classification,',\"children\":['))
      if(IS_FIRST){
        out = paste0(out,paste0('{\"attribute\":\"',attr , '\",\"cut\":',cut,',\"classification\":',classification,',\"children\":['))
        IS_FIRST = FALSE
      }
      else{
        out = paste0(out,paste0('{\"attribute\":\"',attr , '\",\"cut\":',cut,',\"classification\":',classification,',\"children\":['))
        
      }
     
    }
    if(tree_struc_info[curr_node,]$var == '<leaf>'){
      attr = ''
      cut = '0'
      classification = strsplit(plotted_tree$labs[as.integer( row.names(tree_struc_info %>% subset(node_id == as.integer(dfs_list[i]))))], "\\n")[[1]][1] 
      children = 'null'
      if(length(dfs_list)==1){
        if(strsplit(plotted_tree$labs[1], "\\n")[[1]][1]=="1") classification = "true" else classification = "false"
        out = paste0(out,paste0('{\"attribute\":\"',attr , '\",\"cut\":',as.double(cut),',\"classification\":',classification,',\"children\":null}]}'))
        return(out)
      }
      #print(paste0('[{\"attribute\":\"',attr , '\",\"cut\":',cut,',\"classification\":',classification,',\"children\":null'))
      if(!is_right){
        out = paste0(out,paste0('{\"attribute\":\"',attr , '\",\"cut\":',as.double(cut),',\"classification\":',classification,',\"children\":null},'))
      }else{
        out = paste0(out,paste0('{\"attribute\":\"',attr , '\",\"cut\":',as.double(cut),',\"classification\":',classification,',\"children\":null}'))
        #out = paste0(out,']}')
      }
      parent_node = as.integer(tree_struc[which(tree_struc$child2 == tree_struc_info[i,]$node_id),]$nodeid)
      
      #If parent is right child
      int_right_idx = i %in% int_node_list$child2
      for(k in nrow(int_node_list):1){
        if(k == nrow(int_node_list)-1 && !int_node_list[k+1,]$child2 %in% int_node_list$nodeid) is_leaf = TRUE
        if(int_node_list[k,1] %in% nodes_covered && int_node_list[k,2] %in% nodes_covered && int_node_list[k,3] %in% nodes_covered){
          if((!int_node_list[k,]$child1 %in% int_node_list$nodeid) &&(!int_node_list[k,]$child2 %in% int_node_list$nodeid)){
            int_node_list <- int_node_list[-k,]
              if(count(int_node_list)$n > 1 || i != length(dfs_list))
                  out = paste0(out,']},')
              else
                out = paste0(out,']}')
          }
        }
        
      }

    }

  }
  out = paste0(out,']}')
  return(out)
  
}
