(*datatype tree = Empty
              | Node of tree * tree*)

datatype 'a evenList = ENil
                  | ECons of 'a -> oddList -> evenList
and 'a oddList = OCons of 'a -> evenList -> oddList
