library(data.tree)
library(dplyr)
library(DT)
library(rpart)


generator <- function(cval,filename){
  
  
Total_observations = cval
file_name = "add"
#Retrieving data from the files
path <- paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/data/add.bpl.data')
data <- as.data.frame(read.table(path,sep = ','))     

curr_data_count = count(data)
#Retrieving attributes
attr_path <-  paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/data/add.bpl.attributes')
attr <- as.data.frame(read.table(attr_path, sep = ',',fill = TRUE))
attr$V2 = as.character(attr$V2)
attr[nrow(attr)+1,] =  c('int','label',NA)
colnames(data) <- attr[,2]   

attr[attr=="int"] <- "integer"
attr[attr=="cat"] <- "integer"


#Handling labels
data[data=="false"] <- 0
data[data=="true"] <- 1
data[data=="?"] <- sample(0:1,count(filter(data,data$label=="?"))$n,replace = TRUE)

new_data = data.frame(data)
new_data = new_data[0,]

new_data = new_data %>%  filter(label==2)

#Combing data with respective attributes
iter= Total_observations
for (i in 1:iter) {
  new_observation = c()
  
  for (j in 1:nrow(attr)) {
    new_feature =sample(min(data[[j]]):max(data[[j]]),1)
    new_observation=append(new_observation,new_feature)
  }
  new_data[nrow(new_data)+1,]= new_observation
}
data= new_data

new_data["label"][new_data["label"] == 0] <- 'false'
new_data["label"][new_data["label"] == 1] <- 'true' 

all_equal(new_data, new_data,ignore_row_order = TRUE)

new_data = new_data[ order(as.numeric(row.names(new_data))), ]
write.table(new_data,sep=",",file=paste0(dirname(rstudioapi::getSourceEditorContext()$path),"/",Total_observations,filename,"_True_generated_add.data"),row.names = FALSE,col.names = FALSE,quote = FALSE)

copy_data = new_data
data = new_data
#-------------------------------------------------------------------------------


#Creating implications

no_implications = 0.4*Total_observations

imp_indices = sample(1:Total_observations,no_implications)

imp_dataset = data[rownames(data)%in%imp_indices,]


x=split(imp_dataset, imp_dataset$label)

True_imp = as.integer(row.names(x$true))
False_imp = as.integer(row.names(x$false))


non_imp_data = filter(data,data$label != "?")
y=split(non_imp_data, non_imp_data$label)
True_non_imp_data = as.integer(row.names(y$true))
Fale_non_imp_data = as.integer(row.names(y$false))
  
n_pairs = length(imp_indices)+3
imp_list = c()


#TRUE-TRUE PAIRS
LHS = sample(1:length(True_imp),as.integer(n_pairs/6),replace = TRUE)
RHS = sample(1:length(True_imp),as.integer(n_pairs/6),replace = TRUE)
T_df=data.frame(LHS = True_imp[LHS], RHS = True_imp[RHS])   

#FALSE-FALSE PAIRS
LHS = sample(1:length(False_imp),as.integer(n_pairs/4),replace = TRUE)
RHS = sample(1:length(False_imp),as.integer(n_pairs/4),replace = TRUE)
F_df = data.frame(LHS = False_imp[LHS], RHS = False_imp[RHS])   

#FALSE-TRUE PAIRS
LHS = sample(1:length(False_imp),as.integer(n_pairs/4),replace = TRUE)
RHS = sample(1:length(True_imp),as.integer(n_pairs/4),replace = TRUE)
FT_df = data.frame(LHS = False_imp[LHS], RHS = True_imp[RHS]) 


#From non-implication data

#TRUE-TRUE PAIRS
LHS = sample(1:length(True_non_imp_data),as.integer(n_pairs/3),replace = TRUE)
RHS = sample(1:length(True_imp),as.integer(n_pairs/3),replace = TRUE)
NIT_df=data.frame(LHS = True_non_imp_data[LHS], RHS = True_imp[RHS])   

#TRUE-TRUE PAIRS
RHS = sample(1:length(True_non_imp_data),as.integer(n_pairs/3),replace = TRUE)
LHS = sample(1:length(True_imp),as.integer(n_pairs/3),replace = TRUE)
INT_df=data.frame(LHS = True_imp[LHS], RHS = True_non_imp_data[RHS]) 

#FALSE-FALSE PAIRS
LHS = sample(1:length(False_imp),as.integer(n_pairs/3),replace = TRUE)
RHS = sample(1:length(Fale_non_imp_data),as.integer(n_pairs/3),replace = TRUE)
INF_df = data.frame(LHS = False_imp[LHS], RHS = Fale_non_imp_data[RHS])

#FALSE-FALSE PAIRS
RHS = sample(1:length(False_imp),as.integer(n_pairs/3),replace = TRUE)
LHS = sample(1:length(Fale_non_imp_data),as.integer(n_pairs/3),replace = TRUE)
NIF_df = data.frame(RHS = False_imp[RHS], LHS = Fale_non_imp_data[LHS])

#FALSE-TRUE PAIRS
LHS = sample(1:length(False_imp),as.integer(n_pairs/3),replace = TRUE)
RHS = sample(1:length(True_non_imp_data),as.integer(n_pairs/3),replace = TRUE)
INFT_df = data.frame(LHS = False_imp[LHS], RHS = True_non_imp_data[RHS]) 

#FALSE-TRUE PAIRS
LHS = sample(1:length(Fale_non_imp_data),as.integer(n_pairs/6),replace = TRUE)
RHS = sample(1:length(True_imp),as.integer(n_pairs/6),replace = TRUE)
NIFT_df = data.frame(LHS = Fale_non_imp_data[LHS], RHS = True_imp[RHS]) 

  
  imp_list = rbind(T_df,F_df)
  imp_list = rbind(imp_list,FT_df)
  imp_list = rbind(imp_list,NIT_df)
  imp_list = rbind(imp_list,INT_df)
  imp_list = rbind(imp_list,NIF_df)
  imp_list = rbind(imp_list,INF_df)
  imp_list = rbind(imp_list,INFT_df)
  imp_list = rbind(imp_list,NIFT_df)
  
  imp_list =  filter(imp_list,imp_list$LHS!=imp_list$RHS)
  imp_list = unique.data.frame(imp_list)
  #data=copy_data
  #copy_data[row.names(copy_data) %in% imp_list$LHS,]$label =  "?"
  #copy_data[row.names(copy_data) %in% imp_list$RHS,]$label = "?"

  
#data file
  imp_indices= imp_indices[imp_indices %in% imp_list$LHS]
  imp_indices= imp_indices[imp_indices %in% imp_list$RHS]
  
  data[rownames(data) %in% imp_indices, ]$label = "?" 
  #data$label = as.logical(data$label)
  #.data file    
  write.table(data,sep=",",file=paste0(dirname(rstudioapi::getSourceEditorContext()$path),"/",Total_observations,filename,"_generated_add.bpl.data"),row.names = FALSE,col.names = FALSE,quote = FALSE)
  
imp_list$LHS = imp_list$LHS -1
imp_list$RHS = imp_list$RHS -1
  
#.horn file

write.table(imp_list,sep=",",file=paste0(dirname(rstudioapi::getSourceEditorContext()$path),"/",Total_observations,filename,"_generated_add.bpl.horn"),row.names = FALSE,col.names = FALSE,quote = FALSE)



  #Actual tree
  
tree <- rpart(label~.,data=copy_data,method='class', parms = list(split = "gini"),control=rpart.control(minsplit=2,minbucket=1,cp=0.001))
  
rpart.plot::rpart.plot(tree)

#Predicted tree
}

Total_observations = 20
for(i in 1:20){
  generator(Total_observations,i)
}

