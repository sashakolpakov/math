import OAI.RepresentationTheory.Weil.AdelicSplitting.TestSpace

/-! # Field Transport -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FieldTransport.LocalAnalysis

noncomputable section

/-! Change of local-field coordinates for the actual Bruhat space. -/

theorem schwartzBruhat_comp_fieldAddEquiv
    {k l : Type} [NormedField k] [NormedField l] {m n : ℕ}
    (e : Local.FunctionsMetaplectic.Construction.Position k m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position l n)
    {f : Local.FunctionsMetaplectic.Construction.Position l n → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat l n) :
    f ∘ e ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, a, φ, rfl⟩
      · exact Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
          (hf.1.comp_continuous e.continuous) (hf.2.comp_homeomorph e.toHomeomorph)
      · exact Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem (a.trans e.symm) φ
  | zero => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat k m).zero_mem
  | add f g _ _ hf hg => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat k m).add_mem hf hg
  | smul c f _ hf => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat k m).smul_mem c hf

def positionFieldEquiv
    {k l : Type} [NormedField k] [NormedField l] (n : ℕ)
    (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) :
    Local.FunctionsMetaplectic.Construction.Position k n ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position l n where
  toFun x i := e (x i)
  invFun x i := e.symm (x i)
  left_inv x := funext (fun i => e.symm_apply_apply (x i))
  right_inv x := funext (fun i => e.apply_symm_apply (x i))
  map_add' x y := funext (fun i => e.map_add (x i) (y i))
  continuous_toFun := continuous_pi (fun i => he.comp (continuous_apply i))
  continuous_invFun := continuous_pi (fun i => hi.comp (continuous_apply i))

theorem quadratic_field_map
    {k l : Type} [Field k] [Field l] {n : ℕ}
    (e : k →+* l) (B : Matrix (Fin n) (Fin n) k) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.quadratic (B.map e) (fun i => e (x i)) = e (Local.FunctionsMetaplectic.Construction.quadratic B x) := by
  simp only [Local.FunctionsMetaplectic.Construction.quadratic, map_div₀, map_sum, map_mul, Matrix.map_apply]
  rw [map_ofNat]

theorem quadratic_stability_fieldTransport
    {k l : Type} [NormedField k] [NormedField l] {n : ℕ}
    (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm)
    (ψ : AddChar k ℂ)
    (hs : ∀ (B : Matrix (Fin n) (Fin n) l) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat l n),
      Local.FunctionsMetaplectic.Construction.quadraticOperator (ψ.compAddMonoidHom e.symm.toAddMonoidHom) B f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat l n)
    (B : Matrix (Fin n) (Fin n) k) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  let p := positionFieldEquiv n e he hi
  let f' : Local.FunctionsMetaplectic.Construction.schwartzBruhat l n :=
    ⟨f.val ∘ p.symm, schwartzBruhat_comp_fieldAddEquiv p.symm f.property⟩
  have h := schwartzBruhat_comp_fieldAddEquiv p (hs (B.map e) f')
  convert h using 1
  funext x
  change ψ (Local.FunctionsMetaplectic.Construction.quadratic B x) * f.val x =
    ψ (e.symm (Local.FunctionsMetaplectic.Construction.quadratic (B.map e) (fun i => e (x i)))) * f.val (p.symm (p x))
  have hq : Local.FunctionsMetaplectic.Construction.quadratic (B.map e) (fun i => e (x i)) = e (Local.FunctionsMetaplectic.Construction.quadratic B x) :=
    quadratic_field_map e.toRingHom B x
  rw [hq, e.symm_apply_apply, p.symm_apply_apply]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FieldTransport.LocalAnalysis
