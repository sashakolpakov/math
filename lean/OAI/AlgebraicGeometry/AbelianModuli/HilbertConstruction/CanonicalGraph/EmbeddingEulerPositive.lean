import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.LineBundleSectionDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Euler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LineBundleSections

/-! # Embedding Euler Positive -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Euler coefficient of an actual positive graph-bundle power embedding is strictly positive, using its actual generating sections at the zero point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.degreePower_sections_pos
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (x : X)
    [Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower E.degree).sheaf)] :
    0 < Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower E.degree).sheaf) := by
  let e := (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some
  let h := Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso p e
  have : Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj E.power.sheaf) :=
    Module.Finite.equiv h.symm
  obtain ⟨i, hi⟩ := E.covers x
  have hp := Generated.LineBundleSectionDimension.lineBundle_sections_finrank_pos_of_nonvanishing p E.power (E.sections i) x hi
  exact h.finrank_eq ▸ hp

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_embeddedPower_euler_pos
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) :
    0 < CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom
      (A.graphBundle.tensorPower E.degree).sheaf := by
  have hunit : IsUnit (N : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K))))
  have := A.graphBundle_positivePower_sections_finite_overField E.degree
  let x : A.abelian.scheme.left := η[A.abelian.scheme].left (Classical.ofNonempty : Spec (.of K))
  rw [A.graphBundle_positivePower_euler_eq_sections hN hunit E.degree E.degree_pos]
  exact Int.natCast_pos.mpr (E.degreePower_sections_pos A.abelian.scheme.hom x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
