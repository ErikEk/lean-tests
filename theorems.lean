def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem oneplusoneistwo : OnePlusOneIsTwo := rfl
theorem onplusoneistwo : 1 + 1 = 2 := by
    decide

theorem andImpliesOr : A ∧ B → A ∨ B :=
    fun andEvidence =>
        match andEvidence with
        | And.intro a b => Or.inl a

theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide
