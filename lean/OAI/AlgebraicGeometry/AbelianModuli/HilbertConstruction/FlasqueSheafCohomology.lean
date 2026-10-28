import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveSheafFlasqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyExact

/-! # Flasque Sheaf Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueSheafCohomology.ZariskiCohomology.FlasqueAcyclicity

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

noncomputable abbrev injectiveCokernelSequence
    {X : TopCat.{u}} (F : InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.AbSheaf X) : ShortComplex (InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.AbSheaf X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))

theorem injectiveCokernelSequence_shortExact
    {X : TopCat.{u}} (F : InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.AbSheaf X) :
    (injectiveCokernelSequence F).ShortExact := by
  let : Mono (injectiveCokernelSequence F).f := by
    change Mono (Injective.ι F)
    infer_instance
  exact ShortComplex.ShortExact.mk
    (ShortComplex.cokernelSequence_exact (Injective.ι F))

theorem exists_injectiveCokernel_class
    {X : TopCat.{u}} {Z F : InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.AbSheaf X} {n : ℕ}
    (c : Abelian.Ext Z F (n + 1)) :
    ∃ q : Abelian.Ext Z (cokernel (Injective.ι F)) n,
      q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c := by
  have hc : c.comp (Abelian.Ext.mk₀ (Injective.ι F)) rfl = 0 :=
    Abelian.Ext.eq_zero_of_injective _
  exact Abelian.Ext.covariant_sequence_exact₁ Z
    (injectiveCokernelSequence_shortExact F) c hc rfl

/-- Every positive-degree cohomology group of a flasque abelian sheaf is
subsingleton. The proof uses the actual injective-cokernel sequence: its
injective middle term is flasque, its cokernel remains flasque, and the base
case is the section-surjectivity theorem for a short exact sequence with
flasque kernel. -/
theorem flasqueSheaf_H_succ_subsingleton
    {X : TopCat.{u}} (F : InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.AbSheaf X) [TopCat.Sheaf.IsFlasque F]
    (n : ℕ) : Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  induction n generalizing F with
  | zero =>
      refine subsingleton_of_forall_eq 0 fun c ↦ ?_
      obtain ⟨q, hq⟩ := exists_injectiveCokernel_class c
      let S := injectiveCokernelSequence F
      have hS : S.ShortExact := injectiveCokernelSequence_shortExact F
      have : Epi (S.g.hom.app (op (⊤ : Opens X))) :=
        TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
      obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
        (inferInstance : Epi (S.g.hom.app (op (⊤ : Opens X))))
        (CategoryTheory.Sheaf.H.equiv₀ S.X₃
          (isTerminalTop : IsTerminal (⊤ : Opens X)) q)
      let y := (CategoryTheory.Sheaf.H.equiv₀ S.X₂
        (isTerminalTop : IsTerminal (⊤ : Opens X))).symm t
      have hy : CategoryTheory.Sheaf.H.map S.g 0 y = q := by
        apply (CategoryTheory.Sheaf.H.equiv₀ S.X₃
          (isTerminalTop : IsTerminal (⊤ : Opens X))).injective
        rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
        simpa only [y, AddEquiv.apply_symm_apply] using ht
      rw [← hq, ← hy]
      change (y.comp (Abelian.Ext.mk₀ S.g) rfl).comp hS.extClass rfl = 0
      calc
        _ = y.comp ((Abelian.Ext.mk₀ S.g).comp hS.extClass
            (zero_add 1)) (zero_add 1) := by
          simpa only using (Abelian.Ext.comp_assoc y
            (Abelian.Ext.mk₀ S.g) hS.extClass rfl rfl rfl)
        _ = 0 := by rw [hS.comp_extClass, Abelian.Ext.comp_zero]
  | succ n ih =>
      refine subsingleton_of_forall_eq 0 fun c ↦ ?_
      obtain ⟨q, hq⟩ := exists_injectiveCokernel_class c
      let S := injectiveCokernelSequence F
      let : TopCat.Sheaf.IsFlasque S.X₂ :=
        InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.injectiveSheaf_isFlasque S.X₂
      let : TopCat.Sheaf.IsFlasque S.X₃ :=
        TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
          (injectiveCokernelSequence_shortExact F)
      have hqzero : q = 0 := by
        let : Subsingleton (CategoryTheory.Sheaf.H S.X₃ (n + 1)) :=
          ih S.X₃
        exact Subsingleton.elim _ _
      rw [← hq, hqzero, Abelian.Ext.zero_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueSheafCohomology.ZariskiCohomology.FlasqueAcyclicity
