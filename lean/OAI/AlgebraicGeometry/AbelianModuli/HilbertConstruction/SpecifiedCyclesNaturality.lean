import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomologySpecifiedCycles

/-! # Specified Cycles Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecifiedCyclesNaturality

noncomputable section

/-! Naturality of homology computed with specified cycle kernels and cokernels. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v
variable {V : Type u} [Category.{v} V] [Abelian V]

def homologySpecifiedCyclesData (S : ShortComplex V)
    {Z : V} (i : Z ⟶ S.X₂) (wi : i ≫ S.g = 0)
    (hi : IsLimit (KernelFork.ofι i wi)) (a : S.X₁ ⟶ Z) (ha : a ≫ i = S.f) :
    S.LeftHomologyData := by
  have hf : hi.lift (KernelFork.ofι S.f S.zero) = a := by
    apply Fork.IsLimit.hom_ext hi
    exact (Fork.IsLimit.lift_ι hi).trans ha.symm
  exact {
    K := Z
    H := cokernel a
    i := i
    π := cokernel.π a
    wi := wi
    hi := hi
    wπ := by rw [hf]; exact cokernel.condition a
    hπ := by
      subst a
      exact cokernelIsCokernel _ }

theorem homologySpecifiedCyclesData_f' (S : ShortComplex V)
    {Z : V} (i : Z ⟶ S.X₂) (wi : i ≫ S.g = 0)
    (hi : IsLimit (KernelFork.ofι i wi)) (a : S.X₁ ⟶ Z) (ha : a ≫ i = S.f) :
    (homologySpecifiedCyclesData S i wi hi a ha).f' = a := by
  change hi.lift (KernelFork.ofι S.f S.zero) = a
  apply Fork.IsLimit.hom_ext hi
  exact (Fork.IsLimit.lift_ι hi).trans ha.symm

theorem homologySpecifiedCyclesData_iso (S : ShortComplex V)
    {Z : V} (i : Z ⟶ S.X₂) (wi : i ≫ S.g = 0)
    (hi : IsLimit (KernelFork.ofι i wi)) (a : S.X₁ ⟶ Z) (ha : a ≫ i = S.f) :
    (homologySpecifiedCyclesData S i wi hi a ha).homologyIso =
      HomologySpecifiedCycles.homologySpecifiedCyclesIso S i wi hi a ha := by
  have hf : hi.lift (KernelFork.ofι S.f S.zero) = a := by
    apply Fork.IsLimit.hom_ext hi
    exact (Fork.IsLimit.lift_ι hi).trans ha.symm
  subst a
  rfl

theorem homologySpecifiedCyclesIso_naturality
    {S T : ShortComplex V} (φ : S ⟶ T)
    {Z W : V} (i : Z ⟶ S.X₂) (wi : i ≫ S.g = 0)
    (hi : IsLimit (KernelFork.ofι i wi)) (a : S.X₁ ⟶ Z) (ha : a ≫ i = S.f)
    (j : W ⟶ T.X₂) (wj : j ≫ T.g = 0)
    (hj : IsLimit (KernelFork.ofι j wj)) (b : T.X₁ ⟶ W) (hb : b ≫ j = T.f)
    (z : Z ⟶ W) (hz : z ≫ j = i ≫ φ.τ₂) (hab : a ≫ z = φ.τ₁ ≫ b) :
    ShortComplex.homologyMap φ ≫ (HomologySpecifiedCycles.homologySpecifiedCyclesIso T j wj hj b hb).hom =
      (HomologySpecifiedCycles.homologySpecifiedCyclesIso S i wi hi a ha).hom ≫
        cokernel.map a b φ.τ₁ z hab := by
  let hS := homologySpecifiedCyclesData S i wi hi a ha
  let hT := homologySpecifiedCyclesData T j wj hj b hb
  let γ : ShortComplex.LeftHomologyMapData φ hS hT := {
    φK := z
    φH := cokernel.map a b φ.τ₁ z hab
    commi := hz
    commf' := by
      change (homologySpecifiedCyclesData S i wi hi a ha).f' ≫ z =
        φ.τ₁ ≫ (homologySpecifiedCyclesData T j wj hj b hb).f'
      rw [homologySpecifiedCyclesData_f', homologySpecifiedCyclesData_f']
      exact hab
    commπ := cokernel.π_desc _ _ _ }
  have hγ := γ.homologyMap_comm
  change ShortComplex.homologyMap φ ≫ (homologySpecifiedCyclesData T j wj hj b hb).homologyIso.hom =
    (homologySpecifiedCyclesData S i wi hi a ha).homologyIso.hom ≫ cokernel.map a b φ.τ₁ z hab at hγ
  simpa only [homologySpecifiedCyclesData_iso] using hγ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecifiedCyclesNaturality
