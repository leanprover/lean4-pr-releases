example {p : Prop} (h : True → p) : p := by
  simp (discharger := skip) [h]

