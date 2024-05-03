rm(list=ls())

library(chron)
library(colorspace)
library(mime)
library(dichromat)
library(munsell)
library(labeling)
library(rlang)
library(stringi)
library(evaluate)
library(highr)
library(markdown)
library(yaml)
library(backports)
library(jsonlite)
library(digest)
library(plyr)
library(reshape2)
library(scales)
library(tibble)
library(lazyeval)
library(RColorBrewer)
library(stringr)
library(knitr)
library(magrittr)
library(checkmate)
library(htmlwidgets)
library(viridisLite)
library(Rcpp)
library(Formula)
library(ggplot2)
library(latticeExtra)
library(acepack)
library(gtable)
library(gridExtra)
library(data.table)
library(htmlTable)
library(viridis)
library(htmltools)
library(base64enc)
library(minqa)
library(RcppEigen)
library(lme4)
library(SparseM)
library(MatrixModels)
library(pbkrtest)
library(quantreg)
library(car)
library(htmlTable)
library(Hmisc)
library(survival)
library(foreign)
library(bitops)
library(caTools)
library(gplots)
library(ROCR)
library(RODBC)
library(compareGroups)
library(nlme)
library(vcd)
library(psy)
library(irr)
library(boot)
library(tibble)
library(haven)
library(icenReg)
library(arm)
library(standardize)
library(MASS)
library(sandwich)   
library(lmtest)
library(gam)
library(smoothHR)
library(meta)
library(metafor)
library(mgcv)
library(gratia)
library(MuMIn)
library(plotrix)
library(tidyr)
library(nephro)


### GUAPAS ###
##############

guapa<-function(x)
{
  redondeo<-ifelse(abs(x)<0.00001,signif(x,1),
                   ifelse(abs(x)<0.0001,signif(x,1),
                          ifelse(abs(x)<0.001,signif(x,1),
                                 ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                        ifelse(abs(x)<1,sprintf("%.2f",round(x,2)),
                                               ifelse(abs(x)<10,sprintf("%.2f",round(x,2)),
                                                      ifelse(abs(x)<100,sprintf("%.1f",round(x,1)),
                                                             ifelse(abs(x)>=100,round(x,0),round(x,0)))))))))
  return(redondeo)
}

ic_guapa<-function(x,y,z)
{
  ic<-paste(x," [",y,"; ",z,"]",sep="")
  return(ic)
}

ic_guapa2<-function(x,y,z)
{
  ic<-paste(x," (",y," to ",z,")",sep="")
  return(ic)
}

pval_guapa<-function(x)
{
  pval<-ifelse(x<0.00001,"<0.00001",
               ifelse(x<0.001,"<0.001",
                      ifelse(abs(x)<0.01,sprintf("%.3f",round(x,3)),
                             ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                    ifelse(abs(x)<1,sprintf("%.3f",round(x,3)),guapa(x))))))
  return(pval)
}

pval_guapa2<-function(x)
{
  pval<-ifelse(x<0.00001," < 0.00001",
               ifelse(x<0.001," < 0.001",
                      ifelse(abs(x)<0.01,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),
                             ifelse(abs(x)<0.1,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),
                                    ifelse(abs(x)<1,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),guapa(x))))))
  return(pval)
}

mean_ic_guapa <- function(x, na.rm=FALSE) 
{
  if (na.rm) x <- na.omit(x)
  se<-sqrt(var(x)/length(x))
  z<-qnorm(1-0.05/2)
  media<-mean(x)
  ic95a<-guapa(media-(z*se))
  ic95b<-guapa(media+(z*se))
  media<-guapa(media)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

mean_sd_guapa <- function(x) 
{
  media<-guapa(mean(x, na.rm=TRUE))
  sd<-guapa(sd(x, na.rm=TRUE))
  end<-paste(media," (",sd,")",sep="")
  return(end)
}

beta_se_ic_guapa <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

beta_se_ic_guapa2 <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa2(media,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa2 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa2(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa3 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-round(exp(x),3)
  ic95a<-round(exp(x-(z*y)),3)
  ic95b<-round(exp(x+(z*y)),3)
  ic_ok<-ic_guapa2(hr,ic95a,ic95b)
  return(ic_ok)
}

header.true <- function(df)
{
  names(df) <- as.character(unlist(df[1,]))
  df[-1,]
}

z<-qnorm(1-0.05/2)

closest<-function(xv,sv){
  xv[which(abs(xv-sv)==min(abs(xv-sv)))] }

# Suppress scientific notation for coefficients (no "4e-04", instead "0.0004")
options(scipen=999)


setwd("C:/.../PREDIMED_drugs")

dir.create("./Outputs")
dir.create("./Outputs/splines")
dir.create("./Outputs/splines/backup")
dir.create("./Outputs/forestplots")


############################
### CREATION OF DATABASE ###
############################

load("C:/.../predimed_bbdd.RData")

dat<-rename.vars(dat,
                 from=c("escolar01","hipertrigli01",
                        "kcal_total01","kcal_total03","kcal_total04","kcal_total05","kcal_total06","kcal_total07","kcal_total08","kcal_total09","kcal_total10",
                        "f_antiepilepticos01", "f_antiepilepticos03", "f_antiepilepticos04", "f_antiepilepticos05", 
                        "f_antiepilepticos06", "f_antiepilepticos07", "f_antiepilepticos08", "f_antiepilepticos09", 
                        "f_antiepilepticos10", "f_antideptot01", "f_antideptot03", 
                        "f_antideptot04", "f_antideptot05", "f_antideptot06", "f_antideptot07", "f_antideptot08", 
                        "f_antideptot09", "f_antideptot10", "f_ansioltot01", "f_ansioltot03", "f_ansioltot04", 
                        "f_ansioltot05", "f_ansioltot06", "f_ansioltot07", "f_ansioltot08", "f_ansioltot09", 
                        "f_ansioltot10", "f_antipstot01", "f_antipstot03", "f_antipstot04", "f_antipstot05", 
                        "f_antipstot06", "f_antipstot07", "f_antipstot08", "f_antipstot09", "f_antipstot10"),
                 to=c("escolar00","hipertg00",
                      "kcal00","kcal01","kcal02","kcal03","kcal04","kcal05","kcal06","kcal07","kcal08",
                      "f_epil00","f_epil01","f_epil02","f_epil03","f_epil04","f_epil05","f_epil06","f_epil07","f_epil08",
                      "f_dep00","f_dep01","f_dep02","f_dep03","f_dep04","f_dep05","f_dep06","f_dep07","f_dep08",
                      "f_anx00","f_anx01","f_anx02","f_anx03","f_anx04","f_anx05","f_anx06","f_anx07","f_anx08",
                      "f_psyc00","f_psyc01","f_psyc02","f_psyc03","f_psyc04","f_psyc05","f_psyc06","f_psyc07","f_psyc08"))

dat$alcoholg00<-dat$alcoholg01

temp<-dat[,c("id","prop_score01","prop_score02","idcluster2","parejas",
             "escolar00","hipertg00","f_ultcontact_nejm",
             "f_epil00","f_epil01","f_epil02","f_epil03","f_epil04","f_epil05","f_epil06","f_epil07","f_epil08",
             "f_dep00","f_dep01","f_dep02","f_dep03","f_dep04","f_dep05","f_dep06","f_dep07","f_dep08",
             "f_anx00","f_anx01","f_anx02","f_anx03","f_anx04","f_anx05","f_anx06","f_anx07","f_anx08",
             "f_psyc00","f_psyc01","f_psyc02","f_psyc03","f_psyc04","f_psyc05","f_psyc06","f_psyc07","f_psyc08",
             "kcal00","alcoholg00")]


dat<-spss.get("C:/.../bbdd_predimed_20101201.sav",
              use.value.labels=FALSE,to.data.frame=TRUE,allow="_")

dat<-rename.vars(dat,
                 from=c("diabetes0","hipercol0","hta0","imc1","edad0",
                        "getota_1","getota_3","getota_4","getota_5","getota_6","getota_7","getota_8","getota_9","getota_10",
                        "datinclu","datseg3","datseg4","datseg5","datseg6","datseg7","datseg8","datseg9","datseg10"),
                 to=c("diabetes00","hipercolest00","hta00","bmi00","edad",
                      "af00","af01","af02","af03","af04","af05","af06","af07","af08",
                      "seg00","seg01","seg02","seg03","seg04","seg05","seg06","seg07","seg08"))

dat$af_dx<-rowMeans(dat[,c("af01","af02","af03","af04","af05","af06","af07","af08")], na.rm=TRUE)-dat$af00

vars01<-c("seg00","seg01","seg02","seg03","seg04","seg05","seg06","seg07","seg08")

for(i in 1:length(vars01))
  
{
  dat[,vars01[i]]<-chron(as.numeric(as.Date(dat[,vars01[i]]/86400-as.numeric(as.Date("1970-01-01")-as.Date("1582-10-14")),
                                            origin="1970-01-01")),format="d/m/y")
  dat[,vars01[i]]<-with(dat,ifelse(as.numeric(dat[,vars01[i]])>as.numeric(as.Date("2010-12-01")),NA,dat[,vars01[i]]))
  dat[,vars01[i]]<-chron(as.numeric(as.Date(dat[,vars01[i]],origin="1970-01-01")),format="d/m/y")
}

vars01<-c("seg00","seg01","seg02","seg03","seg04","seg05","seg06","seg07","seg08")
vars02<-c("toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08")

for(i in 1:length(vars01))
  
{
  dat[,vars02[i]]<-dat[,vars01[i]]-dat$seg00
}

dat$toseg00<-as.numeric(dat$toseg00)

dat$tabaco00<-with(dat,ifelse(tabaco0==1,1,
                              ifelse(tabaco0==2,2,
                                     ifelse(tabaco0==3,2,
                                            ifelse(tabaco0==4,2,
                                                   ifelse(tabaco0==5,0,
                                                          ifelse(tabaco0==9,NA,NA)))))))
# 0=No fumadores, 1=Fumadores, 2=Exfumadores

dat$obesidad00<-with(dat,ifelse(bmi00<25,0,
                                ifelse(bmi00<30,1,
                                       ifelse(bmi00>=30,2,NA))))

dat<-dat[,c("id","sexo","edad","nodo","grup_int",
            "diabetes00","hipercolest00","hta00","tabaco00","bmi00","obesidad00",
            "af00","af01","af02","af03","af04","af05","af06","af07","af08","af_dx",
            "seg00","seg01","seg02","seg03","seg04","seg05","seg06","seg07","seg08",
            "toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08")]


p14<-spss.get("C:/.../pred_p14.sav",
              use.value.labels=FALSE,to.data.frame=TRUE,allow="_")

p14<-rename.vars(p14,
                 from=c("p14_01_nejm","p14_03_nejm","p14_04_nejm","p14_05_nejm",
                        "p14_06_nejm","p14_07_nejm","p14_08_nejm","p14totm_9","p14totm_10"),
                 to=c("dmed00","dmed01","dmed02","dmed03","dmed04","dmed05","dmed06","dmed07","dmed08"))
p14$dmed07<-with(p14,ifelse(dmed07==0,NA,dmed07))
p14$dmed08<-with(p14,ifelse(dmed08==0,NA,dmed08))
p14$dmed_dx<-rowMeans(p14[,c("dmed01","dmed02","dmed03","dmed04","dmed05","dmed06","dmed07","dmed08")], na.rm=TRUE)-p14$dmed00

p14<-p14[,c("id",
            "dmed00","dmed01","dmed02","dmed03","dmed04","dmed05","dmed06","dmed07","dmed08","dmed_dx")]

dat<-merge2(dat,temp,by.id=c("id"),all.x=TRUE,sort=FALSE)
dat<-merge2(dat,p14,by.id=c("id"),all.x=TRUE,sort=FALSE)
temp<-NULL
p14<-NULL


vars00<-c("toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08",
          "toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08",
          "toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08",
          "toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08",
          "toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08",
          "toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08",
          "toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08")
vars01<-c("f_epil00","f_epil01","f_epil02","f_epil03","f_epil04","f_epil05","f_epil06","f_epil07","f_epil08",
          "f_dep00","f_dep01","f_dep02","f_dep03","f_dep04","f_dep05","f_dep06","f_dep07","f_dep08",
          "f_anx00","f_anx01","f_anx02","f_anx03","f_anx04","f_anx05","f_anx06","f_anx07","f_anx08",
          "f_psyc00","f_psyc01","f_psyc02","f_psyc03","f_psyc04","f_psyc05","f_psyc06","f_psyc07","f_psyc08",
          "dmed00","dmed01","dmed02","dmed03","dmed04","dmed05","dmed06","dmed07","dmed08",
          "af00","af01","af02","af03","af04","af05","af06","af07","af08",
          "kcal00","kcal01","kcal02","kcal03","kcal04","kcal05","kcal06","kcal07","kcal08")

for(i in 1:length(vars01))
  
{
  dat[,vars01[i]]<-with(dat,ifelse(is.na(dat[,vars00[i]]),NA,dat[,vars01[i]]))
}


dat$dmed01_lx<-dat$dmed00
dat$dmed02_lx<-rowMeans(dat[,c("dmed00","dmed01")], na.rm=TRUE)
dat$dmed03_lx<-rowMeans(dat[,c("dmed00","dmed01","dmed02")], na.rm=TRUE)
dat$dmed04_lx<-rowMeans(dat[,c("dmed00","dmed01","dmed02","dmed03")], na.rm=TRUE)
dat$dmed05_lx<-rowMeans(dat[,c("dmed00","dmed01","dmed02","dmed03","dmed04")], na.rm=TRUE)
dat$dmed06_lx<-rowMeans(dat[,c("dmed00","dmed01","dmed02","dmed03","dmed04","dmed05")], na.rm=TRUE)
dat$dmed07_lx<-rowMeans(dat[,c("dmed00","dmed01","dmed02","dmed03","dmed04","dmed05","dmed06")], na.rm=TRUE)
dat$dmed08_lx<-rowMeans(dat[,c("dmed00","dmed01","dmed02","dmed03","dmed04","dmed05","dmed06","dmed07")], na.rm=TRUE)
dat$af01_lx<-dat$af00
dat$af02_lx<-rowMeans(dat[,c("af00","af01")], na.rm=TRUE)
dat$af03_lx<-rowMeans(dat[,c("af00","af01","af02")], na.rm=TRUE)
dat$af04_lx<-rowMeans(dat[,c("af00","af01","af02","af03")], na.rm=TRUE)
dat$af05_lx<-rowMeans(dat[,c("af00","af01","af02","af03","af04")], na.rm=TRUE)
dat$af06_lx<-rowMeans(dat[,c("af00","af01","af02","af03","af04","af05")], na.rm=TRUE)
dat$af07_lx<-rowMeans(dat[,c("af00","af01","af02","af03","af04","af05","af06")], na.rm=TRUE)
dat$af08_lx<-rowMeans(dat[,c("af00","af01","af02","af03","af04","af05","af06","af07")], na.rm=TRUE)
dat$kcal01_lx<-dat$kcal00
dat$kcal02_lx<-rowMeans(dat[,c("kcal00","kcal01")], na.rm=TRUE)
dat$kcal03_lx<-rowMeans(dat[,c("kcal00","kcal01","kcal02")], na.rm=TRUE)
dat$kcal04_lx<-rowMeans(dat[,c("kcal00","kcal01","kcal02","kcal03")], na.rm=TRUE)
dat$kcal05_lx<-rowMeans(dat[,c("kcal00","kcal01","kcal02","kcal03","kcal04")], na.rm=TRUE)
dat$kcal06_lx<-rowMeans(dat[,c("kcal00","kcal01","kcal02","kcal03","kcal04","kcal05")], na.rm=TRUE)
dat$kcal07_lx<-rowMeans(dat[,c("kcal00","kcal01","kcal02","kcal03","kcal04","kcal05","kcal06")], na.rm=TRUE)
dat$kcal08_lx<-rowMeans(dat[,c("kcal00","kcal01","kcal02","kcal03","kcal04","kcal05","kcal06","kcal07")], na.rm=TRUE)


vars01<-c("toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08")

for(i in 1:length(vars01))
  
{
  dat[,vars01[i]]<-as.numeric(dat[,vars01[i]])
}


dat$f_epil_inicio<-dat$f_epil00
dat$f_epil_seg<-rowSums(!is.na(dat[,grep("f_epil0", names(dat))]))
dat$f_epil_any<-as.integer(apply(dat[,grep("f_epil0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$f_dep_inicio<-dat$f_dep00
dat$f_dep_seg<-rowSums(!is.na(dat[,grep("f_dep0", names(dat))]))
dat$f_dep_any<-as.integer(apply(dat[,grep("f_dep0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$f_anx_inicio<-dat$f_anx00
dat$f_anx_seg<-rowSums(!is.na(dat[,grep("f_anx0", names(dat))]))
dat$f_anx_any<-as.integer(apply(dat[,grep("f_anx0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$f_psyc_inicio<-dat$f_psyc00
dat$f_psyc_seg<-rowSums(!is.na(dat[,grep("f_psyc0", names(dat))]))
dat$f_psyc_any<-as.integer(apply(dat[,grep("f_psyc0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))


x<-dat[,c("id","f_epil00","f_epil01","f_epil02","f_epil03","f_epil04","f_epil05","f_epil06","f_epil07","f_epil08")]
write.table(x,"./Outputs/data/f_epil.csv",
            sep=";",col.names=TRUE,row.names=FALSE)
x<-dat[,c("id","f_dep00","f_dep01","f_dep02","f_dep03","f_dep04","f_dep05","f_dep06","f_dep07","f_dep08")]
write.table(x,"./Outputs/data/f_dep.csv",
            sep=";",col.names=TRUE,row.names=FALSE)
x<-dat[,c("id","f_anx00","f_anx01","f_anx02","f_anx03","f_anx04","f_anx05","f_anx06","f_anx07","f_anx08")]
write.table(x,"./Outputs/data/f_anx.csv",
            sep=";",col.names=TRUE,row.names=FALSE)
x<-dat[,c("id","f_psyc00","f_psyc01","f_psyc02","f_psyc03","f_psyc04","f_psyc05","f_psyc06","f_psyc07","f_psyc08")]
write.table(x,"./Outputs/data/f_psyc.csv",
            sep=";",col.names=TRUE,row.names=FALSE)
x<-NULL


f_epil<-read.csv2("./Outputs/Data/f_epil_revisado.csv",header=TRUE,sep=";",dec=".")
dat<-merge2(dat,f_epil,by.id=c("id"),all.x=TRUE,sort=FALSE)
f_epil<-NULL
f_dep<-read.csv2("./Outputs/Data/f_dep_revisado.csv",header=TRUE,sep=";",dec=".")
dat<-merge2(dat,f_dep,by.id=c("id"),all.x=TRUE,sort=FALSE)
f_dep<-NULL
f_anx<-read.csv2("./Outputs/Data/f_anx_revisado.csv",header=TRUE,sep=";",dec=".")
dat<-merge2(dat,f_anx,by.id=c("id"),all.x=TRUE,sort=FALSE)
f_anx<-NULL
f_psyc<-read.csv2("./Outputs/Data/f_psyc_revisado.csv",header=TRUE,sep=";",dec=".")
dat<-merge2(dat,f_psyc,by.id=c("id"),all.x=TRUE,sort=FALSE)
f_psyc<-NULL


vars01<-c("f_epil_d","f_dep_d","f_anx_d","f_psyc_d")

for(i in 1:length(vars01))
  
{
  dat[,vars01[i]]<-as.numeric(dat[,vars01[i]])
  dat[,vars01[i]]<-with(dat,ifelse(is.na(dat[,vars01[i]]),0,dat[,vars01[i]]))
}

dat$okseg01<-with(dat,ifelse(is.na(toseg01),0,1))
dat$okseg02<-with(dat,ifelse(is.na(toseg02),0,1))
dat$okseg03<-with(dat,ifelse(is.na(toseg03),0,1))
dat$okseg04<-with(dat,ifelse(is.na(toseg04),0,1))
dat$okseg05<-with(dat,ifelse(is.na(toseg05),0,1))
dat$okseg06<-with(dat,ifelse(is.na(toseg06),0,1))
dat$okseg07<-with(dat,ifelse(is.na(toseg07),0,1))
dat$okseg08<-with(dat,ifelse(is.na(toseg08),0,1))

dat$okseg01_left<-with(dat,ifelse(okseg01==1,0,NA))
dat$okseg02_left<-with(dat,ifelse((okseg02==1 & okseg01==1),1,
                                  ifelse((okseg02==1 & okseg01==0),0,NA)))
dat$okseg03_left<-with(dat,ifelse((okseg03==1 & okseg02==1),2,
                                  ifelse((okseg03==1 & okseg02==0 & okseg01==1),1,
                                         ifelse((okseg03==1 & okseg02==0 & okseg01==0),0,NA))))
dat$okseg04_left<-with(dat,ifelse((okseg04==1 & okseg03==1),3,
                                  ifelse((okseg04==1 & okseg03==0 & okseg02==1),2,
                                         ifelse((okseg04==1 & okseg03==0 & okseg02==0 & okseg01==1),1,
                                                ifelse((okseg04==1 & okseg03==0 & okseg02==0 & okseg01==0),0,NA)))))
dat$okseg05_left<-with(dat,ifelse((okseg05==1 & okseg04==1),4,
                                  ifelse((okseg05==1 & okseg04==0 & okseg03==1),3,
                                         ifelse((okseg05==1 & okseg04==0 & okseg03==0 & okseg02==1),2,
                                                ifelse((okseg05==1 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==1),1,
                                                       ifelse((okseg05==1 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==0),0,NA))))))
dat$okseg06_left<-with(dat,ifelse((okseg06==1 & okseg05==1),5,
                                  ifelse((okseg06==1 & okseg05==0 & okseg04==1),4,
                                         ifelse((okseg06==1 & okseg05==0 & okseg04==0 & okseg03==1),3,
                                                ifelse((okseg06==1 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==1),2,
                                                       ifelse((okseg06==1 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==1),1,
                                                              ifelse((okseg06==1 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==0),0,NA)))))))
dat$okseg07_left<-with(dat,ifelse((okseg07==1 & okseg06==1),6,
                                  ifelse((okseg07==1 & okseg06==0 & okseg05==1),5,
                                         ifelse((okseg07==1 & okseg06==0 & okseg05==0 & okseg04==1),4,
                                                ifelse((okseg07==1 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==1),3,
                                                       ifelse((okseg07==1 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==1),2,
                                                              ifelse((okseg07==1 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==1),1,
                                                                     ifelse((okseg07==1 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==0),0,NA))))))))
dat$okseg08_left<-with(dat,ifelse((okseg08==1 & okseg07==1),7,
                                  ifelse((okseg08==1 & okseg07==0 & okseg06==1),6,
                                         ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==1),5,
                                                ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==0 & okseg04==1),4,
                                                       ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==1),3,
                                                              ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==1),2,
                                                                     ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==1),1,
                                                                            ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==0),0,NA)))))))))

vars01<-c("f_ultcontact")
vars02<-c("seg08")
vars03<-c("seg07")
vars04<-c("seg06")
vars05<-c("seg05")
vars06<-c("seg04")
vars07<-c("seg03")
vars08<-c("seg02")
vars09<-c("seg01")

for(i in 1:length(vars01))
  
{
  dat[,vars01[i]]<-with(dat,ifelse(!is.na(dat[,vars02[i]]),seg08,
                                   ifelse(is.na(dat[,vars02[i]]) & !is.na(dat[,vars03[i]]),seg07,
                                          ifelse(is.na(dat[,vars02[i]]) & is.na(dat[,vars03[i]]) & !is.na(dat[,vars04[i]]),seg06,
                                                 ifelse(is.na(dat[,vars02[i]]) & is.na(dat[,vars03[i]]) & is.na(dat[,vars04[i]]) & !is.na(dat[,vars05[i]]),seg05,
                                                        ifelse(is.na(dat[,vars02[i]]) & is.na(dat[,vars03[i]]) & is.na(dat[,vars04[i]]) & is.na(dat[,vars05[i]]) & !is.na(dat[,vars06[i]]),seg04,
                                                               ifelse(is.na(dat[,vars02[i]]) & is.na(dat[,vars03[i]]) & is.na(dat[,vars04[i]]) & is.na(dat[,vars05[i]]) & is.na(dat[,vars06[i]]) & !is.na(dat[,vars07[i]]),seg03,
                                                                      ifelse(is.na(dat[,vars02[i]]) & is.na(dat[,vars03[i]]) & is.na(dat[,vars04[i]]) & is.na(dat[,vars05[i]]) & is.na(dat[,vars06[i]]) & is.na(dat[,vars07[i]]) & !is.na(dat[,vars08[i]]),seg02,
                                                                             ifelse(is.na(dat[,vars02[i]]) & is.na(dat[,vars03[i]]) & is.na(dat[,vars04[i]]) & is.na(dat[,vars05[i]]) & is.na(dat[,vars06[i]]) & is.na(dat[,vars07[i]]) & is.na(dat[,vars08[i]]) & !is.na(dat[,vars09[i]]),seg01,NA)))))))))
  class(dat[,vars01[i]])<-"Date"
  dat[,vars01[i]]<-chron(as.numeric(as.Date(dat[,vars01[i]],origin="1970-01-01")),format="d/m/y")
}


vars01<-c("f_epil_d","f_dep_d","f_anx_d","f_psyc_d")
vars02<-NULL
vars03<-NULL
vars04<-NULL
vars05<-NULL
vars06<-NULL
vars07<-c("f_ultcontact","f_ultcontact","f_ultcontact","f_ultcontact")

for(i in 1:length(vars01))
  
{
  vars02<-c(vars02,paste("to",vars01[i],sep=""))
  vars03<-c(vars03,paste(vars01[i],"_left",sep=""))
  vars04<-c(vars04,paste("to",vars01[i],"_left",sep=""))
  vars05<-c(vars05,paste("to",vars01[i],"_right",sep=""))
  vars06<-c(vars06,paste(vars01[i],"_when",sep=""))
}


for(i in 1:length(vars01))
  
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,toseg01,
                                   ifelse(dat[,vars01[i]]==2,toseg02,
                                          ifelse(dat[,vars01[i]]==3,toseg03,
                                                 ifelse(dat[,vars01[i]]==4,toseg04,
                                                        ifelse(dat[,vars01[i]]==5,toseg05,
                                                               ifelse(dat[,vars01[i]]==6,toseg06,
                                                                      ifelse(dat[,vars01[i]]==7,toseg07,
                                                                             ifelse(dat[,vars01[i]]==8,toseg08,dat[,vars07[i]]-seg00)))))))))
}

for(i in 1:length(vars01))
  
{
  dat[,vars03[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,okseg01_left,
                                   ifelse(dat[,vars01[i]]==2,okseg02_left,
                                          ifelse(dat[,vars01[i]]==3,okseg03_left,
                                                 ifelse(dat[,vars01[i]]==4,okseg04_left,
                                                        ifelse(dat[,vars01[i]]==5,okseg05_left,
                                                               ifelse(dat[,vars01[i]]==6,okseg06_left,
                                                                      ifelse(dat[,vars01[i]]==7,okseg07_left,
                                                                             ifelse(dat[,vars01[i]]==8,okseg08_left,0)))))))))
  
  
}

for(i in 1:length(vars03))
  
{
  
  dat[,vars04[i]]<-with(dat,ifelse(dat[,vars03[i]]==0,0,
                                   ifelse(dat[,vars03[i]]==1,toseg01,
                                          ifelse(dat[,vars03[i]]==2,toseg02,
                                                 ifelse(dat[,vars03[i]]==3,toseg03,
                                                        ifelse(dat[,vars03[i]]==4,toseg04,
                                                               ifelse(dat[,vars03[i]]==5,toseg05,
                                                                      ifelse(dat[,vars03[i]]==6,toseg06,
                                                                             ifelse(dat[,vars03[i]]==7,toseg07,dat[,vars07[i]]-seg00)))))))))
}


for(i in 1:length(vars01))
  
{  
  dat[,vars05[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,toseg01,
                                   ifelse(dat[,vars01[i]]==2,toseg02,
                                          ifelse(dat[,vars01[i]]==3,toseg03,
                                                 ifelse(dat[,vars01[i]]==4,toseg04,
                                                        ifelse(dat[,vars01[i]]==5,toseg05,
                                                               ifelse(dat[,vars01[i]]==6,toseg06,
                                                                      ifelse(dat[,vars01[i]]==7,toseg07,
                                                                             ifelse(dat[,vars01[i]]==8,toseg08,Inf)))))))))
  
  
}

for(i in 1:length(vars01))
  
{  
  dat[,vars06[i]]<-dat[,vars01[i]]
}

for(i in 1:length(vars01))
  
{
  dat[,vars01[i]]<-with(dat,ifelse(dat[,vars01[i]]==0,0,1))
}



### FLOW CHART ###

dim(dat)[1] #7447
length(which(dat$f_dep_seg<=1)) #-328
dat<-subset2(dat,"f_dep_seg>1") 
dim(dat)[1] #7119
length(which(is.na(dat$dmed00))) #-22
dat<-subset2(dat,"!is.na(dmed00)")
dim(dat)[1] #7097
length(which(is.na(dat$kcal00))) #-34
dat<-subset2(dat,"!is.na(kcal00)")
dim(dat)[1] #7063

dat$dmed_long<-rowMeans(dat[,c("dmed00","dmed01","dmed02","dmed03","dmed04","dmed05","dmed06","dmed07","dmed08")], na.rm=TRUE)
dat$af_long<-rowMeans(dat[,c("af00","af01","af02","af03","af04","af05","af06","af07","af08")], na.rm=TRUE)
dat$kcal_long<-rowMeans(dat[,c("kcal00","kcal01","kcal02","kcal03","kcal04","kcal05","kcal06","kcal07","kcal08")], na.rm=TRUE)

dat$dmed00_cat2<-with(dat,ifelse(dmed00<10,0,1))
dat$dmed00_cat4<-with(dat,ifelse(dmed00<8,0,
                                 ifelse(dmed00<10,1,
                                        ifelse(dmed00<12,2,
                                               ifelse(dmed00>=12,3,NA)))))
dat$dmed_long_cat2<-with(dat,ifelse(dmed_long<10,0,1))
dat$dmed_long_cat4<-with(dat,ifelse(dmed_long<8,0,
                                    ifelse(dmed_long<10,1,
                                           ifelse(dmed_long<12,2,
                                                  ifelse(dmed_long>=12,3,NA)))))

dat$af00_cat2<-with(dat,ifelse(af00<100,0,1))
dat$af_long_cat2<-with(dat,ifelse(af_long<100,0,1))

dat$excl01<-with(dat,ifelse(parejas==1 | nodo==4,1,0))
dat$excl02<-with(dat,ifelse(parejas==1 | nodo==4 | nodo==1,1,0))


attributes(dat$edad)$label<-NULL
attributes(dat$sexo)$label<-NULL
attributes(dat$diabetes00)$label<-NULL
attributes(dat$hipercolest00)$label<-NULL
attributes(dat$hta00)$label<-NULL

save(dat,file="./predimed_drugs_ps.RData")



################
### ANALYSES ###
################


##########################
### DESCRIPTIVE TABLES ###
##########################

dir.create("C:/.../PREDIMED_drugs/Outputs/Descriptive")
load("./predimed_drugs_ps.RData")

xxx<-dat[,c("id","edad","sexo","escolar00",
            "dmed_long_cat2","af_long_cat2","dmed00","af00",
            "diabetes00","hipercolest00","hipertg00","hta00","tabaco00","obesidad00","alcoholg00","kcal00")]
xxx$sel<-1

tab2<-NULL
tab2<-createTable(compareGroups(sel~.
                                -id-dmed_long_cat2-af_long_cat2,
                                xxx, method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercolest00"=3,
                                              "hipertg00"=3,"hta00"=3,"tabaco00"=3,"obesidad00"=3,
                                              "af00"=2,"alcoholg00"=2)),
                  show.n=TRUE, hide.no=0)

dmed_long2<-NULL
dmed_long2<-createTable(compareGroups(dmed_long_cat2~.
                                      -id-sel-af_long_cat2,
                                      xxx, method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercolest00"=3,
                                                    "hipertg00"=3,"hta00"=3,"tabaco00"=3,"obesidad00"=3,
                                                    "af00"=2,"alcoholg00"=2)),
                        show.n=TRUE, hide.no=0)

af_long2<-NULL
af_long2<-createTable(compareGroups(af_long_cat2~.
                                    -id-sel-dmed_long_cat2,
                                    xxx, method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercolest00"=3,
                                                  "hipertg00"=3,"hta00"=3,"tabaco00"=3,"obesidad00"=3,
                                                  "af00"=2,"alcoholg00"=2)),
                      show.n=TRUE, hide.no=0)


long2<-cbind(tab2$descr[,1],dmed_long2$descr[,1:3],af_long2$descr)
colnames(long2)<-c("All","<10 MEDAS",">=10 MEDAS","P-value","<100 METs-min/d",">=100 METs-min/d","P-value","N")
write.table(long2,file="./Outputs/Descriptive/descriptive.csv",sep=";",col.names=NA)


############################################################################
### NUMBER OF PARTICIPANTS WITH LIPID PROFILE VALUES IN THE STUDY VISITS ###
############################################################################

load("./predimed_drugs_ps.RData")

vars01<-c("f_epil00","f_epil01","f_epil02","f_epil03","f_epil04","f_epil05","f_epil06","f_epil07")
vars02<-c("f_dep00","f_dep01","f_dep02","f_dep03","f_dep04","f_dep05","f_dep06","f_dep07")
vars03<-c("f_anx00","f_anx01","f_anx02","f_anx03","f_anx04","f_anx05","f_anx06","f_anx07")
vars04<-c("f_psyc00","f_psyc01","f_psyc02","f_psyc03","f_psyc04","f_psyc05","f_psyc06","f_psyc07")

tab<-NULL
for(i in 1:length(vars01))
  
{
  det1<-length(which(!is.na(dat[,vars01[i]])))
  det2<-length(which(!is.na(dat[,vars02[i]])))
  det3<-length(which(!is.na(dat[,vars03[i]])))
  det4<-length(which(!is.na(dat[,vars04[i]])))
  tab<-rbind(tab,cbind(det1,det2,det3,det4))
}

tab<-t(tab)
rownames(tab)<-c("f_epil","f_dep","f_anx","f_psyc")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years")
write.table(tab,file="./Outputs/Descriptive/rep_measures_values.csv",sep=";",col.names=NA)



###############################
### SURVIVAL ANALYSES: DMED ###
###############################

dir.create("C:/.../PREDIMED_drugs/Outputs/Survival")
dir.create("C:/.../PREDIMED_drugs/Outputs/Survival/dmed")
dir.create("C:/.../PREDIMED_drugs/Outputs/Survival/dmed/backup")
dir.create("C:/.../PREDIMED_drugs/Outputs/Survival/dmed/backup/strat")

load("./predimed_drugs_ps.RData")

dat$edad70<-with(dat,ifelse(edad<70,0,1))
dat$escolar_sup<-with(dat,ifelse(escolar00==1,0,
                                 ifelse(escolar00==2,0,
                                        ifelse(escolar00==3,1,
                                               ifelse(escolar00==9,NA,NA)))))
dat$obesidad200<-with(dat,ifelse(obesidad00==2,1,0))
dat$af00_m<-with(dat,ifelse(af00<=median(dat$af00,na.rm=TRUE),0,1))
dat$alcoholg00_m<-with(dat,ifelse(alcoholg00<=median(dat$alcoholg00,na.rm=TRUE),0,1))
dat$kcal00_m<-with(dat,ifelse(kcal00<=median(dat$kcal00,na.rm=TRUE),0,1))
dat$grup_int2<-with(dat,ifelse(grup_int==3,0,1))
dat$tabaco200<-with(dat,ifelse(tabaco00==0,0,1)) # Never vs ever

z<-qnorm(1-0.05/2)


varsxx<-c("f_epil","f_dep","f_anx","f_psyc")
vars01<-NULL
vars02<-NULL
vars03<-NULL
vars04<-NULL
vars05<-NULL
vars06<-NULL
vars07<-NULL
vars08<-c("Onset of use of antiseizure drugs",
          "Onset of use of antidepressants",
          "Onset of use of anxiolytics",
          "Onset of use of antipsychotic drugs")
vars10<-c(8,8,8,8,8,8) # Most beneficial LTPA range (a posteriori)


for(i in 1:length(varsxx))
{
  vars01<-c(vars01,paste(varsxx[i],"_d",sep=""))
  vars03<-c(vars03,paste(varsxx[i],"_inicio",sep=""))
  vars05<-c(vars05,paste(varsxx[i],"_seg",sep=""))
}

for(i in 1:length(vars01))
{
  vars02<-c(vars02,paste("to",vars01[i],sep=""))
  vars04<-c(vars04,paste(vars01[i],"_when",sep=""))
  vars06<-c(vars06,paste("to",vars01[i],"_left",sep=""))
  vars07<-c(vars07,paste("to",vars01[i],"_right",sep=""))
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,(dat[,vars06[i]]+dat[,vars07[i]])/2,dat[,vars02[i]]))
}


tab<-NULL
tab_ok<-NULL

for(i in 1:length(vars01))
  
{ 
  participants<-length(which(dat[,vars03[i]]==0))
  labelok<-vars08[i]
  datx<-subset2(dat,"dat[,vars03[i]]==0")
  
  datx$dmed_long<-with(datx,ifelse(datx[,vars04[i]]==0,dmed08_lx,
                                   ifelse(datx[,vars04[i]]==1,dmed01_lx,
                                          ifelse(datx[,vars04[i]]==2,dmed02_lx,
                                                 ifelse(datx[,vars04[i]]==3,dmed03_lx,
                                                        ifelse(datx[,vars04[i]]==4,dmed04_lx,
                                                               ifelse(datx[,vars04[i]]==5,dmed05_lx,
                                                                      ifelse(datx[,vars04[i]]==6,dmed06_lx,
                                                                             ifelse(datx[,vars04[i]]==7,dmed07_lx,
                                                                                    ifelse(datx[,vars04[i]]==8,dmed08_lx,NA))))))))))
  dmed_outl<-length(which(datx$dmed_long<5))
  datx<-subset2(datx,"datx$dmed_long>=5")
  samplesize<-dim(datx)[1]
  
  datx$dmed_long2<-with(datx,ifelse(dmed_long<10,0,
                                    ifelse(dmed_long>=10,1,NA)))
  datx$dmed_long4<-with(datx,ifelse(dmed_long<8,0,
                                    ifelse(dmed_long<10,1,
                                           ifelse(dmed_long<12,2,
                                                  ifelse(dmed_long>=12,3,NA)))))
  
  dat2<-subset2(datx,"!is.na(datx$dmed_long)")
  median_time<-ic_guapa(guapa(summary((dat2[,vars02[i]]/365.25))[3]),guapa(summary((dat2[,vars02[i]]/365.25))[2]),guapa(summary((dat2[,vars02[i]]/365.25))[5]))
  
  mod02<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~dmed_long+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+alcoholg00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=dat2)
  hr_dmed_long_cont<-intervals(mod02)[1,1]
  ic95a_dmed_long_cont<-intervals(mod02)[1,2]
  ic95b_dmed_long_cont<-intervals(mod02)[1,3]
  pval_dmed_long_cont<-intervals(mod02)[1,4]
  pval_dmed_long_cont_ex<-intervals(mod02)[1,4]
  hr_dmed_long_cont_ok<-guapa(hr_dmed_long_cont)
  ic95a_dmed_long_cont_ok<-guapa(ic95a_dmed_long_cont)
  ic95b_dmed_long_cont_ok<-guapa(ic95b_dmed_long_cont)
  coef_dmed_long_cont<-ic_guapa2(hr_dmed_long_cont_ok,ic95a_dmed_long_cont_ok,ic95b_dmed_long_cont_ok)
  pval_dmed_long_cont<-pval_guapa(pval_dmed_long_cont)
  
  dat2$xxx<-dat2$dmed_long/1
  modxx<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~xxx+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+alcoholg00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=dat2)
  coef_dmed_long_cont2<-ic_guapa2(guapa(intervals(modxx)[1,1]),guapa(intervals(modxx)[1,2]),guapa(intervals(modxx)[1,3]))
  
  mod03<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~C(as.factor(dmed_long4),base=1)+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+alcoholg00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=dat2)
  hr_dmed_long_q2<-intervals(mod03)[1,1]
  ic95a_dmed_long_q2<-intervals(mod03)[1,2]
  ic95b_dmed_long_q2<-intervals(mod03)[1,3]
  pval_dmed_long_q2<-intervals(mod03)[1,4]
  hr_dmed_long_q2_ok<-guapa(hr_dmed_long_q2)
  ic95a_dmed_long_q2_ok<-guapa(ic95a_dmed_long_q2)
  ic95b_dmed_long_q2_ok<-guapa(ic95b_dmed_long_q2)
  coef_dmed_long_q2<-ic_guapa2(hr_dmed_long_q2_ok,ic95a_dmed_long_q2_ok,ic95b_dmed_long_q2_ok)
  pval_dmed_long_q2<-pval_guapa(pval_dmed_long_q2)
  hr_dmed_long_q3<-intervals(mod03)[2,1]
  ic95a_dmed_long_q3<-intervals(mod03)[2,2]
  ic95b_dmed_long_q3<-intervals(mod03)[2,3]
  pval_dmed_long_q3<-intervals(mod03)[2,4]
  hr_dmed_long_q3_ok<-guapa(hr_dmed_long_q3)
  ic95a_dmed_long_q3_ok<-guapa(ic95a_dmed_long_q3)
  ic95b_dmed_long_q3_ok<-guapa(ic95b_dmed_long_q3)
  coef_dmed_long_q3<-ic_guapa2(hr_dmed_long_q3_ok,ic95a_dmed_long_q3_ok,ic95b_dmed_long_q3_ok)
  pval_dmed_long_q3<-pval_guapa(pval_dmed_long_q3)
  hr_dmed_long_q4<-intervals(mod03)[3,1]
  ic95a_dmed_long_q4<-intervals(mod03)[3,2]
  ic95b_dmed_long_q4<-intervals(mod03)[3,3]
  pval_dmed_long_q4<-intervals(mod03)[3,4]
  hr_dmed_long_q4_ok<-guapa(hr_dmed_long_q4)
  ic95a_dmed_long_q4_ok<-guapa(ic95a_dmed_long_q4)
  ic95b_dmed_long_q4_ok<-guapa(ic95b_dmed_long_q4)
  coef_dmed_long_q4<-ic_guapa2(hr_dmed_long_q4_ok,ic95a_dmed_long_q4_ok,ic95b_dmed_long_q4_ok)
  pval_dmed_long_q4<-pval_guapa(pval_dmed_long_q4)
  
  mod03<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~C(as.factor(dmed_long2),base=1)+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+alcoholg00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=dat2)
  hr_dmed_long_m<-intervals(mod03)[1,1]
  ic95a_dmed_long_m<-intervals(mod03)[1,2]
  ic95b_dmed_long_m<-intervals(mod03)[1,3]
  pval_dmed_long_m<-intervals(mod03)[1,4]
  hr_dmed_long_m_ok<-guapa(hr_dmed_long_m)
  ic95a_dmed_long_m_ok<-guapa(ic95a_dmed_long_m)
  ic95b_dmed_long_m_ok<-guapa(ic95b_dmed_long_m)
  coef_dmed_long_m<-ic_guapa2(hr_dmed_long_m_ok,ic95a_dmed_long_m_ok,ic95b_dmed_long_m_ok)
  pval_dmed_long_m<-pval_guapa(pval_dmed_long_m)
  
  mod04<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~dmed_long4+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+alcoholg00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=dat2)
  hr_dmed_long_qi<-intervals(mod04)[1,1]
  ic95a_dmed_long_qi<-intervals(mod04)[1,2]
  ic95b_dmed_long_qi<-intervals(mod04)[1,3]
  pval_dmed_long_qi<-intervals(mod04)[1,4]
  hr_dmed_long_qi_ok<-guapa(hr_dmed_long_qi)
  ic95a_dmed_long_qi_ok<-guapa(ic95a_dmed_long_qi)
  ic95b_dmed_long_qi_ok<-guapa(ic95b_dmed_long_qi)
  coef_dmed_long_qi<-ic_guapa2(hr_dmed_long_qi_ok,ic95a_dmed_long_qi_ok,ic95b_dmed_long_qi_ok)
  pval_dmed_long_qi<-pval_guapa(pval_dmed_long_qi)
  
  nval_dmed_long_ca<-length(which(dat2[,vars01[i]]==1&!is.na(dat2$dmed_long)))
  nval_dmed_long_co<-length(which(dat2[,vars01[i]]==0&!is.na(dat2$dmed_long)))
  nval_dmed_long_cont<-paste("'",nval_dmed_long_ca,"/",nval_dmed_long_ca+nval_dmed_long_co,sep="")
  nval_dmed_long_q<-table(dat2[,vars01[i]],by=dat2$dmed_long4)
  nval_dmed_long_q1<-paste("'",nval_dmed_long_q[2,1],"/",nval_dmed_long_q[2,1]+nval_dmed_long_q[1,1],sep="")
  nval_dmed_long_q2<-paste("'",nval_dmed_long_q[2,2],"/",nval_dmed_long_q[2,2]+nval_dmed_long_q[1,2],sep="")
  nval_dmed_long_q3<-paste("'",nval_dmed_long_q[2,3],"/",nval_dmed_long_q[2,3]+nval_dmed_long_q[1,3],sep="")
  nval_dmed_long_q4<-paste("'",nval_dmed_long_q[2,4],"/",nval_dmed_long_q[2,4]+nval_dmed_long_q[1,4],sep="")
  nval_dmed_long_m<-table(dat2[,vars01[i]],by=dat2$dmed_long2)
  nval_dmed_long_m1<-paste("'",nval_dmed_long_m[2,1],"/",nval_dmed_long_m[2,1]+nval_dmed_long_m[1,1],sep="")
  nval_dmed_long_m2<-paste("'",nval_dmed_long_m[2,2],"/",nval_dmed_long_m[2,2]+nval_dmed_long_m[1,2],sep="")
  
  dat3<-subset2(datx,"datx$dmed_long<vars10[i]")
  dat3$xxx<-dat3$dmed_long/1
  modxx<-coxph(Surv(dat3[,vars02[i]], dat3[,vars01[i]])~xxx+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+alcoholg00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=dat3)
  hr_dmed_long_opt<-intervals(modxx)[1,1]
  ic95a_dmed_long_opt<-intervals(modxx)[1,2]
  ic95b_dmed_long_opt<-intervals(modxx)[1,3]
  pval_dmed_long_opt<-intervals(modxx)[1,4]
  pval_dmed_long_opt_ex<-intervals(modxx)[1,4]
  hr_dmed_long_opt_ok<-guapa(hr_dmed_long_opt)
  ic95a_dmed_long_opt_ok<-guapa(ic95a_dmed_long_opt)
  ic95b_dmed_long_opt_ok<-guapa(ic95b_dmed_long_opt)
  coef_dmed_long_opt<-ic_guapa2(hr_dmed_long_opt_ok,ic95a_dmed_long_opt_ok,ic95b_dmed_long_opt_ok)
  pval_dmed_long_opt<-pval_guapa(pval_dmed_long_opt)
  
  
  # SPLINES #
  
  mfit<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~pspline(dmed_long, df=4)+as.factor(grup_int)+cluster(idcluster2)
              +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
              +af00+kcal00+alcoholg00+prop_score01+prop_score02,
              na.action=na.exclude, method="breslow",data=dat2)
  
  p_lin_dmed<-pval_dmed_long_cont
  p_nonlin_dmed<-pval_guapa(summary(mfit)$coefficients[2,6])
  p_lrtest_dmed<-pval_guapa(lrtest(mod02,mfit)[2,5])
  
  p_lin2<-ifelse(p_lin_dmed=="<0.001"," < 0.001",
                 ifelse(p_lin_dmed=="<0.00001"," < 0.00001",paste(" = ",p_lin_dmed,sep="")))
  p_nonlin2<-ifelse(p_nonlin_dmed=="<0.001"," < 0.001",
                    ifelse(p_nonlin_dmed=="<0.00001"," < 0.00001",paste(" = ",p_nonlin_dmed,sep="")))
  p_lrtest2<-ifelse(p_lrtest_dmed=="<0.001"," < 0.001",
                    ifelse(p_lrtest_dmed=="<0.00001"," < 0.00001",paste(" = ",p_lrtest_dmed,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$dmed_long
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data)<-c("x","yest","lci","uci")
  plot.data$coef<-ic_guapa2(guapa(plot.data$y),guapa(plot.data$lci),guapa(plot.data$uci))
  min_dmed_val<-guapa(plot.data$x[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))])
  min_dmed_coef<-plot.data$coef[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))]
  plot.datax<-plot.data[,c("x","coef")]
  plot.data$coef<-NULL
  plot.data<-subset2(plot.data,"plot.data$uci<=4")
  colnames(plot.datax)<-c("dmed","HR")
  write.table(plot.datax,file=paste("./Outputs/Survival/dmed/backup/",vars01[i],".csv",sep=""),sep=";",col.names=TRUE,row.names=FALSE)
  
  namefile<-paste("./Outputs/Survival/dmed/",vars01[i],".jpg",sep="")
  labely<-paste(vars08[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("p-value for linearity",p_lin2,
             "\nHR for +1 score point (range: 5-14 points):\n",coef_dmed_long_cont2,
             "\np-value for non-linearity",p_lrtest2,
             "\nHR for +1 score point (range: 5-",vars10[i]," points):\n",coef_dmed_long_opt,sep="")
  
  figure<-ggplot(data=plot.data, aes_string(x=plot.data$x, y=plot.data$y)) + 
    geom_ribbon(aes_string(ymin=plot.data$lci, ymax=plot.data$uci), alpha=0.25, fill='#D55E00') +
    geom_line(aes_string(x=plot.data$x, y=plot.data$y), color='#D55E00') +
    geom_hline(yintercept=1, linetype=2) +
    theme_bw() +
    #scale_x_continuous(breaks=c(5:14)) +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Cumulative average of MedDiet adherence\n(MedDiet adherence score points)"),y=labely) +
    annotate("text", x=max(plot.data$x,na.rm=TRUE)*0.98, y=max(plot.data$uci,na.rm=TRUE), label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=16, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=16, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())  
  
  ggsave(filename=namefile,units="px", width=8400, height=8400, dpi=1200, bg="white")
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  tab_ok<-rbind(tab_ok,cbind(median_time,participants,dmed_outl,
                             nval_dmed_long_cont,coef_dmed_long_cont,pval_dmed_long_cont,pval_dmed_long_cont_ex,p_lrtest_dmed,
                             nval_dmed_long_q1,nval_dmed_long_q2,coef_dmed_long_q2,pval_dmed_long_q2,
                             nval_dmed_long_q3,coef_dmed_long_q3,pval_dmed_long_q3,
                             nval_dmed_long_q4,coef_dmed_long_q4,pval_dmed_long_q4,
                             coef_dmed_long_qi,pval_dmed_long_qi,
                             nval_dmed_long_m1,nval_dmed_long_m2,coef_dmed_long_m,pval_dmed_long_m,
                             min_dmed_val,min_dmed_coef,labelok))
  tab<-rbind(tab,cbind(median_time,participants,dmed_outl,
                       nval_dmed_long_cont,hr_dmed_long_cont,ic95a_dmed_long_cont,ic95b_dmed_long_cont,pval_dmed_long_cont,
                       pval_dmed_long_cont_ex,p_lrtest_dmed,
                       nval_dmed_long_q1,nval_dmed_long_q2,hr_dmed_long_q2,ic95a_dmed_long_q2,ic95b_dmed_long_q2,pval_dmed_long_q2,
                       nval_dmed_long_q3,hr_dmed_long_q3,ic95a_dmed_long_q3,ic95b_dmed_long_q3,pval_dmed_long_q3,
                       nval_dmed_long_q4,hr_dmed_long_q4,ic95a_dmed_long_q4,ic95b_dmed_long_q4,pval_dmed_long_q4,
                       hr_dmed_long_qi,ic95a_dmed_long_qi,ic95b_dmed_long_qi,pval_dmed_long_qi,
                       nval_dmed_long_m1,nval_dmed_long_m2,hr_dmed_long_m,ic95a_dmed_long_m,ic95b_dmed_long_m,pval_dmed_long_m,
                       min_dmed_val,min_dmed_coef,labelok))
}

rownames(tab)<-vars01
rownames(tab_ok)<-vars01
write.table(tab_ok,file="./Outputs/Survival/dmed/survival_dmed.csv",sep=";",col.names=NA)
write.table(tab,file="./Outputs/Survival/dmed/forestplots_dmed.csv",sep=";",col.names=NA)



###############################
### SURVIVAL ANALYSES: LTPA ###
###############################

dir.create("C:/.../PREDIMED_drugs/Outputs/Survival/af")
dir.create("C:/.../PREDIMED_drugs/Outputs/Survival/af/backup")
dir.create("C:/.../PREDIMED_drugs/Outputs/Survival/af/backup/strat")

load("./predimed_drugs_ps.RData")

dat$edad70<-with(dat,ifelse(edad<70,0,1))
dat$escolar_sup<-with(dat,ifelse(escolar00==1,0,
                                 ifelse(escolar00==2,0,
                                        ifelse(escolar00==3,1,
                                               ifelse(escolar00==9,NA,NA)))))
dat$obesidad200<-with(dat,ifelse(obesidad00==2,1,0))
dat$af00_m<-with(dat,ifelse(af00<=median(dat$af00,na.rm=TRUE),0,1))
dat$alcoholg00_m<-with(dat,ifelse(alcoholg00<=median(dat$alcoholg00,na.rm=TRUE),0,1))
dat$kcal00_m<-with(dat,ifelse(kcal00<=median(dat$kcal00,na.rm=TRUE),0,1))
dat$grup_int2<-with(dat,ifelse(grup_int==3,0,1))
dat$tabaco200<-with(dat,ifelse(tabaco00==0,0,1)) # Never vs ever

z<-qnorm(1-0.05/2)


varsxx<-c("f_epil","f_dep","f_anx","f_psyc")
vars01<-NULL
vars02<-NULL
vars03<-NULL
vars04<-NULL
vars05<-NULL
vars06<-NULL
vars07<-NULL
vars08<-c("Onset of use of antiseizure drugs",
          "Onset of use of antidepressants",
          "Onset of use of anxiolytics",
          "Onset of use of antipsychotic drugs")
vars10<-c(150,150,150,150) # Most beneficial LTPA range (a posteriori)


for(i in 1:length(varsxx))
{
  vars01<-c(vars01,paste(varsxx[i],"_d",sep=""))
  vars03<-c(vars03,paste(varsxx[i],"_inicio",sep=""))
  vars05<-c(vars05,paste(varsxx[i],"_seg",sep=""))
}

for(i in 1:length(vars01))
{
  vars02<-c(vars02,paste("to",vars01[i],sep=""))
  vars04<-c(vars04,paste(vars01[i],"_when",sep=""))
  vars06<-c(vars06,paste("to",vars01[i],"_left",sep=""))
  vars07<-c(vars07,paste("to",vars01[i],"_right",sep=""))
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,(dat[,vars06[i]]+dat[,vars07[i]])/2,dat[,vars02[i]]))
}


tab<-NULL
tab_ok<-NULL


for(i in 1:length(vars01))
  
{ 
  participants<-length(which(dat[,vars03[i]]==0))
  labelok<-vars08[i]
  datx<-subset2(dat,"dat[,vars03[i]]==0")
  
  datx$dmed_long<-with(datx,ifelse(datx[,vars04[i]]==0,af08_lx,
                                   ifelse(datx[,vars04[i]]==1,af01_lx,
                                          ifelse(datx[,vars04[i]]==2,af02_lx,
                                                 ifelse(datx[,vars04[i]]==3,af03_lx,
                                                        ifelse(datx[,vars04[i]]==4,af04_lx,
                                                               ifelse(datx[,vars04[i]]==5,af05_lx,
                                                                      ifelse(datx[,vars04[i]]==6,af06_lx,
                                                                             ifelse(datx[,vars04[i]]==7,af07_lx,
                                                                                    ifelse(datx[,vars04[i]]==8,af08_lx,NA))))))))))
  dmed_outl<-length(which(datx$dmed_long>1000))
  datx<-subset2(datx,"datx$dmed_long<1000")
  samplesize<-dim(datx)[1]
  
  datx$dmed_long2<-with(datx,ifelse(dmed_long<100,0,
                                    ifelse(dmed_long>=100,1,NA)))
  dat2<-subset2(datx,"!is.na(datx$dmed_long)")
  median_time<-ic_guapa(guapa(summary((dat2[,vars02[i]]/365.25))[3]),guapa(summary((dat2[,vars02[i]]/365.25))[2]),guapa(summary((dat2[,vars02[i]]/365.25))[5]))
  
  dat2$xxx<-dat2$dmed_long/20
  mod02<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~xxx+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
               +dmed00+kcal00+alcoholg00,
               na.action=na.exclude, method="breslow", data=dat2)
  hr_dmed_long_cont<-intervals(mod02)[1,1]
  ic95a_dmed_long_cont<-intervals(mod02)[1,2]
  ic95b_dmed_long_cont<-intervals(mod02)[1,3]
  pval_dmed_long_cont<-intervals(mod02)[1,4]
  pval_dmed_long_cont_ex<-intervals(mod02)[1,4]
  hr_dmed_long_cont_ok<-guapa(hr_dmed_long_cont)
  ic95a_dmed_long_cont_ok<-guapa(ic95a_dmed_long_cont)
  ic95b_dmed_long_cont_ok<-guapa(ic95b_dmed_long_cont)
  coef_dmed_long_cont<-ic_guapa2(hr_dmed_long_cont_ok,ic95a_dmed_long_cont_ok,ic95b_dmed_long_cont_ok)
  pval_dmed_long_cont<-pval_guapa(pval_dmed_long_cont)
  
  mod03<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~C(as.factor(dmed_long2),base=1)+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
               +dmed00+kcal00+alcoholg00,
               na.action=na.exclude, method="breslow", data=dat2)
  hr_dmed_long_m<-intervals(mod03)[1,1]
  ic95a_dmed_long_m<-intervals(mod03)[1,2]
  ic95b_dmed_long_m<-intervals(mod03)[1,3]
  pval_dmed_long_m<-intervals(mod03)[1,4]
  hr_dmed_long_m_ok<-guapa(hr_dmed_long_m)
  ic95a_dmed_long_m_ok<-guapa(ic95a_dmed_long_m)
  ic95b_dmed_long_m_ok<-guapa(ic95b_dmed_long_m)
  coef_dmed_long_m<-ic_guapa2(hr_dmed_long_m_ok,ic95a_dmed_long_m_ok,ic95b_dmed_long_m_ok)
  pval_dmed_long_m<-pval_guapa(pval_dmed_long_m)
  
  nval_dmed_long_ca<-length(which(dat2[,vars01[i]]==1&!is.na(dat2$dmed_long)))
  nval_dmed_long_co<-length(which(dat2[,vars01[i]]==0&!is.na(dat2$dmed_long)))
  nval_dmed_long_cont<-paste("'",nval_dmed_long_ca,"/",nval_dmed_long_ca+nval_dmed_long_co,sep="")
  nval_dmed_long_m<-table(dat2[,vars01[i]],by=dat2$dmed_long2)
  nval_dmed_long_m1<-paste("'",nval_dmed_long_m[2,1],"/",nval_dmed_long_m[2,1]+nval_dmed_long_m[1,1],sep="")
  nval_dmed_long_m2<-paste("'",nval_dmed_long_m[2,2],"/",nval_dmed_long_m[2,2]+nval_dmed_long_m[1,2],sep="")
  
  dat3<-subset2(datx,"datx$dmed_long<vars10[i]")
  dat3$xxx<-dat3$dmed_long/20
  mod02<-coxph(Surv(dat3[,vars02[i]], dat3[,vars01[i]])~xxx+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
               +dmed00+kcal00+alcoholg00,
               na.action=na.exclude, method="breslow", data=dat3)
  hr_dmed_long_opt<-intervals(mod02)[1,1]
  ic95a_dmed_long_opt<-intervals(mod02)[1,2]
  ic95b_dmed_long_opt<-intervals(mod02)[1,3]
  pval_dmed_long_opt<-intervals(mod02)[1,4]
  pval_dmed_long_opt_ex<-intervals(mod02)[1,4]
  hr_dmed_long_opt_ok<-guapa(hr_dmed_long_opt)
  ic95a_dmed_long_opt_ok<-guapa(ic95a_dmed_long_opt)
  ic95b_dmed_long_opt_ok<-guapa(ic95b_dmed_long_opt)
  coef_dmed_long_opt<-ic_guapa2(hr_dmed_long_opt_ok,ic95a_dmed_long_opt_ok,ic95b_dmed_long_opt_ok)
  pval_dmed_long_opt<-pval_guapa(pval_dmed_long_opt)
  
  
  # SPLINES #
  
  mfit<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~pspline(dmed_long, df=4)+as.factor(grup_int)+cluster(idcluster2)
              +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
              +dmed00+kcal00+alcoholg00,
              na.action=na.exclude, method="breslow",data=dat2)
  mod02<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~dmed_long+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)+as.factor(tabaco00)+bmi00
               +dmed00+kcal00+alcoholg00,
               na.action=na.exclude, method="breslow", data=dat2)
  
  p_lin_dmed<-pval_dmed_long_cont
  p_nonlin_dmed<-pval_guapa(summary(mfit)$coefficients[2,6])
  p_lrtest_dmed<-pval_guapa(lrtest(mod02,mfit)[2,5])
  
  p_lin2<-ifelse(p_lin_dmed=="<0.001"," < 0.001",
                 ifelse(p_lin_dmed=="<0.00001"," < 0.00001",paste(" = ",p_lin_dmed,sep="")))
  p_nonlin2<-ifelse(p_nonlin_dmed=="<0.001"," < 0.001",
                    ifelse(p_nonlin_dmed=="<0.00001"," < 0.00001",paste(" = ",p_nonlin_dmed,sep="")))
  p_lrtest2<-ifelse(p_lrtest_dmed=="<0.001"," < 0.001",
                    ifelse(p_lrtest_dmed=="<0.00001"," < 0.00001",paste(" = ",p_lrtest_dmed,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$dmed_long
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data)<-c("x","yest","lci","uci")
  plot.data$coef<-ic_guapa2(guapa(plot.data$y),guapa(plot.data$lci),guapa(plot.data$uci))
  min_dmed_val<-guapa(plot.data$x[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))])
  min_dmed_coef<-plot.data$coef[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))]
  plot.datax<-plot.data[,c("x","coef")]
  plot.data$coef<-NULL
  colnames(plot.datax)<-c("LTPA","HR")
  write.table(plot.datax,file=paste("./Outputs/Survival/af/backup/",vars01[i],".csv",sep=""),sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data)<-c("x","yest","lci","uci")
  plot.data<-subset2(plot.data,"plot.data$uci<=4")
  
  namefile<-paste("./Outputs/Survival/af/",vars01[i],".jpg",sep="")
  labely<-paste(vars08[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("p-value for linearity",p_lin2,
             "\nHR for +20 METs-min/d (range: 0-1000 METs-min/d):\n",coef_dmed_long_cont,
             "\np-value for non-linearity",p_lrtest2,
             "\nHR for +20 METs-min/d (range: 0-",vars10[i]," METs-min/d):\n",coef_dmed_long_opt,sep="")
  
  figure<-ggplot(data=plot.data, aes_string(x=plot.data$x, y=plot.data$y)) + 
    geom_ribbon(aes_string(ymin=plot.data$lci, ymax=plot.data$uci), alpha=0.25, fill="#B31529") +
    geom_line(aes_string(x=plot.data$x, y=plot.data$y), color='#B31529') +
    geom_hline(yintercept=1, linetype=2) +
    theme_bw() +
    #scale_x_continuous(breaks=c(5:14)) +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Leisure-time physical activity\n(cumulative average, METs-min/d)"),y=labely) +
    annotate("text", x=max(plot.data$x,na.rm=TRUE)*0.98, y=max(plot.data$uci,na.rm=TRUE), label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=16, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=16, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())  
  
  ggsave(filename=namefile,units="px", width=8400, height=8400, dpi=1200, bg="white")
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  tab_ok<-rbind(tab_ok,cbind(median_time,participants,dmed_outl,
                             nval_dmed_long_cont,coef_dmed_long_cont,pval_dmed_long_cont,pval_dmed_long_cont_ex,p_lrtest_dmed,
                             nval_dmed_long_m1,nval_dmed_long_m2,coef_dmed_long_m,pval_dmed_long_m,
                             min_dmed_val,min_dmed_coef,labelok))
  tab<-rbind(tab,cbind(median_time,participants,dmed_outl,
                       nval_dmed_long_cont,hr_dmed_long_cont,ic95a_dmed_long_cont,ic95b_dmed_long_cont,pval_dmed_long_cont,
                       pval_dmed_long_cont_ex,p_lrtest_dmed,
                       nval_dmed_long_m1,nval_dmed_long_m2,hr_dmed_long_m,ic95a_dmed_long_m,ic95b_dmed_long_m,pval_dmed_long_m,
                       min_dmed_val,min_dmed_coef,labelok))
}

rownames(tab)<-vars01
rownames(tab_ok)<-vars01
write.table(tab_ok,file="./Outputs/Survival/af/survival_af.csv",sep=";",col.names=NA)
write.table(tab,file="./Outputs/Survival/af/forestplots_af.csv",sep=";",col.names=NA)

