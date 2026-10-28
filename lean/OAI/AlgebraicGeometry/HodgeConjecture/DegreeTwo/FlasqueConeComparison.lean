import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BoundedFlasqueSections
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ConeQuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-! # Flasque Cone Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueConeComparison.Constructions

noncomputable section

/-! Actual sections preserve quasi-isomorphisms between bounded-below flasque complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

theorem moduleSheafBiprod_isFlasque {R : Type} [Ring R] {X : TopCat.{0}}
    (F G : TopCat.Sheaf (ModuleCat.{0} R) X) [TopCat.Sheaf.IsFlasque F] [TopCat.Sheaf.IsFlasque G] :
    TopCat.Sheaf.IsFlasque (F ⊞ G) where
  epi {U W} j := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro s
    let i₁ : F ⟶ F ⊞ G := biprod.inl
    let i₂ : G ⟶ F ⊞ G := biprod.inr
    let p₁ : F ⊞ G ⟶ F := biprod.fst
    let p₂ : F ⊞ G ⟶ G := biprod.snd
    obtain ⟨u,hu⟩ := (ModuleCat.epi_iff_surjective (F.obj.map j)).mp inferInstance (p₁.hom.app W s)
    obtain ⟨v,hv⟩ := (ModuleCat.epi_iff_surjective (G.obj.map j)).mp inferInstance (p₂.hom.app W s)
    refine ⟨i₁.hom.app U u + i₂.hom.app U v, ?_⟩
    have h₁ := ConcreteCategory.congr_hom (i₁.hom.naturality j) u
    have h₂ := ConcreteCategory.congr_hom (i₂.hom.naturality j) v
    change i₁.hom.app W (F.obj.map j u) = (F ⊞ G).obj.map j (i₁.hom.app U u) at h₁
    change i₂.hom.app W (G.obj.map j v) = (F ⊞ G).obj.map j (i₂.hom.app U v) at h₂
    rw [map_add, ← h₁, ← h₂, hu, hv]
    have hid : p₁.hom.app W ≫ i₁.hom.app W + p₂.hom.app W ≫ i₂.hom.app W = 𝟙 _ :=
      congrArg (fun f => f.hom.app W) (biprod.total (X := F) (Y := G))
    exact ConcreteCategory.congr_hom hid s

variable {X : TopCat.{0}}
variable {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℤ} (f : K ⟶ L)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n))

include hK hL

theorem rationalFlasque_mappingCone (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((CochainComplex.mappingCone f).X n) := by
  have := hK (n+1)
  have := hL n
  have := moduleSheafBiprod_isFlasque (K.X (n+1)) (L.X n)
  exact ThomGoodShiftFlasque.Constructions.rationalSheafFlasque_of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n+1) rfl).symm

theorem rationalBoundedFlasqueSections_quasiIso (b : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE b]
    [QuasiIso f] (U : Opens X) :
    QuasiIso (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have := CochainComplex.isStrictlyGE_mappingCone f b b (b-1) (by omega) (by omega)
  have he := (ConeQuasiIso.Constructions.cochainQuasiIso_iff_mappingCone_acyclic f).mp inferInstance
  apply ConeQuasiIso.Constructions.functorQuasiIso_of_mappingCone_acyclic
  exact BoundedFlasqueSections.Constructions.rationalBoundedFlasqueSections_acyclic (CochainComplex.mappingCone f)
    (rationalFlasque_mappingCone f hK hL) (b-1) he U

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueConeComparison.Constructions
