open import Functional.State as St using (Oracle ; FileSystem ; Cmd)

module Functional.Script.Exec (oracle : Oracle) where

open import Data.List using ([] ; _∷_ ; List ; _++_)
open import Functional.State.Helpers (oracle) using (run ; cmdReadNames ; cmdWriteNames)
open import Functional.Build (oracle) using (Build)
open import Functional.File using (FileName)

script : Build → FileSystem → FileSystem
script [] sys = sys
script (x ∷ b) sys = script b (run x sys)

buildReadNames : FileSystem -> Build -> List FileName
buildReadNames _ [] = []
buildReadNames sys (x ∷ b) = (cmdReadNames x sys) ++ buildReadNames (run x sys) b

buildWriteNames : FileSystem -> Build -> List FileName
buildWriteNames _ [] = []
buildWriteNames sys (x ∷ b) = (cmdWriteNames x sys) ++ buildWriteNames (run x sys) b
