(*datatype tree = Empty
              | Node of tree * tree*)

datatype evenList = ENil
                  | ECons of int -> oddList -> evenList
and oddList = OCons of int -> evenList -> oddList
