#Function that builds tree with training data and plots it

Building_tree <- function(training_data,func){
        #Input: 
          #training_data :  observations whose label is determined
          #Func: the categorical variable i.e first column in .data file which determines number of subtrees that need to be constructed 
  
  #In .data file the first field refers to categorical attribute '$func' which tells how many trees to be built.
  
  #sub-setting the training data based on '$func' attribute and building sub trees
  training_data = subset(training_data, training_data$`$func`==func)
  
  
  #We are building tree with the received training data with y = label and all other attributes as x.
  
  #Treating label as boolean variable
  training_data$label <- as.logical(training_data$label)

  
  #Since rpart is throwing error when all the labels belong to TRUE(or FALSE) i.e same label, added this check
  if(length(unique(training_data$label)) ==1){
    tree <- rpart(label ~ . ,data= training_data)
  }
  else{ 
  #Handling tree construction errors here!
  tryCatch(
  tree <- rpart(label~.,data=training_data,method='class', parms = list(split = "gini"),control=rpart.control(minsplit=2,minbucket=1,cp=0.001))
  ,error = function(e){   
    err_msg = "Error : Inconsistent tree"
    stop(err_msg)
  }
  )
   #Since Boogie (C++ tool) only work with integer values; we are rounting the split values 
   tree$splits[,4] = ceiling(as.numeric(tree$splits[,4]))
 }
  
 #Plotting the constructed tree
  rpart.plot(tree,type=4,compress = FALSE,
             extra=101,
             box.palette="GnBu",
             branch.lty=3, 
             shadow.col="gray", 
             nn=TRUE)
  print(tree)
  return(tree)
 
}
