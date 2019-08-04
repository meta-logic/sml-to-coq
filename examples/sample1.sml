(*datatype tree = Empty
              | Node of tree * tree*)

datatype 'a evenList = ENil
                  | ECons of 'a * 'a oddList * 'a evenList
and 'a oddList = OCons of 'a * 'a evenList * 'a oddList
