#!/bin/bash

export COQPATH="coqLibraries/libs"
# Directory where genAllExamples places the .v files
DIR=examples

coqc ${DIR}/misc
coqc ${DIR}/decl_pat  
coqc ${DIR}/filter 
coqc ${DIR}/mutual_rec
coqc ${DIR}/partial
coqc ${DIR}/theorem_generation
coqc ${DIR}/filter
coqc ${DIR}/id
coqc ${DIR}/non_terminating
coqc ${DIR}/terminating
coqc ${DIR}/trees
