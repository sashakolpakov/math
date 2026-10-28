import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CartesianRestrictionVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineClosedSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CohomologyExcision

/-! # Cartesian Global Excision -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A Cartesian Poincare family can be restricted to any parameter open
containing the full inverse image of zero, preserving every coefficient action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

def Dual.Data.DualAbelianData.poincareCartesianGlobalOpenCoefficientIso
    {S T : Scheme.{u}} [T.IsSeparated] [IsLocallyNoetherian T]
    {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
    {t : T ⟶ D.abelian.scheme.left}
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t)
    {R : Type u} [CommRing R] (c : R →+* Γ(P, ⊤))
    (U : T.Opens) (hU : t ⁻¹' Set.range η[D.abelian.scheme].left ⊆ U) (q : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj (D.poincare.pullback a).sheaf ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor ((b ⁻¹ᵁ U).ι.appTop.hom.comp c) q).obj
        ((D.poincare.pullback a).sheaf.restrict (b ⁻¹ᵁ U).ι) := by
  let V : T.Opens := ⟨(t ⁻¹' Set.range η[D.abelian.scheme].left)ᶜ,
    (D.dualZeroSection_range_isClosed.preimage t.continuous).isOpen_compl⟩
  let W := b ⁻¹ᵁ U
  let Z := b ⁻¹ᵁ V
  have hcover : U ⊔ V = ⊤ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      by_cases hy : y ∈ t ⁻¹' Set.range η[D.abelian.scheme].left
      · exact Or.inl (hU hy)
      · exact Or.inr hy
  have hpre : W ⊔ Z = ⊤ := by
    change b ⁻¹ᵁ U ⊔ b ⁻¹ᵁ V = ⊤
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  have hoff (B : T.Opens) (hB : B ≤ V) :
      (B.ι ≫ t) ⁻¹' Set.range η[D.abelian.scheme].left = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (hB x.property) hx
  let L := D.poincare.pullback a
  have hV (n : ℕ) : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.sheaf.restrict Z.ι) n) :=
    D.poincare_cartesian_openRestriction_vanish H V (hoff V le_rfl) n
  have hUV (n : ℕ) : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.sheaf.restrict (W ⊓ Z).ι) n) := by
    change Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.sheaf.restrict (b ⁻¹ᵁ (U ⊓ V)).ι) n)
    exact D.poincare_cartesian_openRestriction_vanish H (U ⊓ V) (hoff _ inf_le_right) n
  exact Linear.CohomologyExcision.coefficientCohomologyTwoOpenExcisionIso c L.sheaf W Z hpre hV hUV q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
