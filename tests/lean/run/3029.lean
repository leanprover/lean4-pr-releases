import Lean.Data.PersistentHashMap
open Lean

example : ((PersistentHashMap.empty : PersistentHashMap Nat Nat)
    |> (·.insert 1 1)
    |> (·.insert 1 1)
    |> (·.size)) = 1 := by native_decide

example : ((PersistentHashMap.empty : PersistentHashMap Nat Nat)
    |> (·.insert 1 1)
    |> (·.insert 2 1)
    |> (·.size)) = 2 := by native_decide
