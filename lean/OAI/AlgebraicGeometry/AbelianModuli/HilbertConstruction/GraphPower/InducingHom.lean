import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SymmetricGraphInducingFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.DivisorPolarization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.PolarizationFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.PolarizedDualFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosureFieldPullbackEquality

/-! # Inducing Hom -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.InducingHom

noncomputable section

/-! A graph-power comparison determines the inducing homomorphism.
Geometric positivity supplies symmetry on field fibers, and the actual
pointed-map detector retains arbitrary, possibly nonreduced, tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

local instance inducingHomPicardGroup (X : Scheme.{u}) : CommGroup (Line.Bundles.LineBundle.IsoClass X) :=
  Picard.Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup X

private theorem inducingLineClass_of_powerIso
    {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (L Q : Line.Bundles.LineBundle A.scheme.left) (d : ℕ)
    (e : L.sheaf ≅ (Q.tensorPower d).sheaf) :
    Picard.PoincareBundle.InducingClass.Bundle.lineClass A.scheme L =
      Picard.PoincareBundle.InducingClass.Bundle.lineClass A.scheme Q ^ d := by
  have he : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf (Q.tensorPower d) := Quotient.sound ⟨e⟩
  have hc : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf Q ^ d :=
    he.trans (Line.Bundles.LineBundle.classOf_tensorPower Q d)
  simp only [Picard.PoincareBundle.InducingClass.Bundle.lineClass, hc, map_pow, div_pow]

/-- The difference of the d-th graph power is the Poincare class of
`[2d]p`, whenever the actual Poincare pairing is symmetric. -/
theorem inducingHom_eq_multiple_of_graphPower_overField
    {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left) (d : ℕ)
    (em : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (eG : L.sheaf ≅ ((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d).sheaf)
    (hs : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ p) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ p) x) :
    A.multiplication (2 * d) ≫ p = m := by
  have hc : Line.Bundles.LineBundle.classOf (D.poincareAt m) =
      Line.Bundles.LineBundle.classOf (D.poincareAt (p ^ (2 * d))) := by
    have h₀ : (Line.Bundles.LineBundle.classOf (D.poincareAt m) : Line.Bundles.LineBundle.IsoClass (A.scheme ⊗ A.scheme).left) =
        Picard.PoincareBundle.InducingClass.Bundle.lineClass A.scheme L :=
      Picard.PoincareBundle.InducingClass.Bundle.class_eq_of_formula A.scheme L (D.poincareAt m) em
    have h₁ := inducingLineClass_of_powerIso A L (PoincareGraph.Bundles.poincareGraphBundle D p) d eG
    have h₂ : Picard.PoincareBundle.InducingClass.Bundle.lineClass A.scheme (PoincareGraph.Bundles.poincareGraphBundle D p) ^ d =
        Line.Bundles.LineBundle.classOf (D.poincareAt (p ^ 2)) ^ d :=
      congrArg (fun c : Line.Bundles.LineBundle.IsoClass (A.scheme ⊗ A.scheme).left => c ^ d)
        (SymmetricGraphInducingFormula.poincareGraph_differenceClass_double D p hs)
    have h₃ : Line.Bundles.LineBundle.classOf (D.poincareAt (p ^ 2)) ^ d =
        Line.Bundles.LineBundle.classOf (D.poincareAt ((p ^ 2) ^ d)) :=
      (D.poincareAt_class_pow A.scheme (p ^ 2) d).symm
    have h₄ : Line.Bundles.LineBundle.classOf (D.poincareAt ((p ^ 2) ^ d)) =
        Line.Bundles.LineBundle.classOf (D.poincareAt (p ^ (2 * d))) :=
      congrArg (fun q : A.scheme ⟶ D.abelian.scheme => Line.Bundles.LineBundle.classOf (D.poincareAt q))
        (pow_mul p 2 d).symm
    exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))
  have hm : m = p ^ (2 * d) := D.poincareAt_class_injective A.scheme hc
  have hp : A.multiplication (2 * d) ≫ p = p ^ (2 * d) := by
    change ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ (2 * d)) ≫ p = _
    rw [MonObj.pow_comp, Category.id_comp]
  exact hp.trans hm.symm

/-- On every test of a fixed Noetherian projective family, an actual
graph-power comparison forces the original inducing equation. -/
theorem polarization_inducingHom_eq_multiple_of_graphPower
    {S : Scheme.{u}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (T : Over S)
    (D : Dual.Data.DualAbelianData (A.pullback T.hom)) (p : PolarizationData.Polarization D δ)
    (level : (A.pullback T.hom).FullLevel N) (hδ : ∀ i, 0 < δ i)
    (m : (A.pullback T.hom).scheme ⟶ D.abelian.scheme)
    (hm : η[(A.pullback T.hom).scheme] ≫ m = η[D.abelian.scheme])
    (L : Line.Bundles.LineBundle (A.pullback T.hom).scheme.left) (d : ℕ)
    (em : (((D.poincareAt m).tensor
      (L.pullback (fst (A.pullback T.hom).scheme (A.pullback T.hom).scheme).left)).tensor
      (L.pullback (snd (A.pullback T.hom).scheme (A.pullback T.hom).scheme).left)).sheaf ≅
        (L.pullback μ[(A.pullback T.hom).scheme].left).sheaf)
    (eG : L.sheaf ≅ ((PoincareGraph.Bundles.poincareGraphBundle D p.isogeny.hom).tensorPower d).sheaf) :
    (A.pullback T.hom).multiplication (2 * d) ≫ p.isogeny.hom = m := by
  let B : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left := ⟨A.pullback T.hom, D, p, level⟩
  let f : (A.pullback T.hom).scheme ⟶ D.abelian.scheme :=
    (A.pullback T.hom).multiplication (2 * d) ≫ p.isogeny.hom
  let : IsMonHom ((A.pullback T.hom).multiplication (2 * d)) := by
    rw [← (A.pullback T.hom).endRing_natCast_hom (2 * d)]
    infer_instance
  have hf : η[(A.pullback T.hom).scheme] ≫ f = η[D.abelian.scheme] :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ p.isogeny.hom)
        (IsMonHom.one_hom ((A.pullback T.hom).multiplication (2 * d)))).trans
        (IsMonHom.one_hom p.isogeny.hom))
  apply Universal.PolarizedDualFieldDetection.universalPolarizedDual_pointedMap_eq_of_fieldPullbacks A A P P T D p level hδ f m hf hm
  apply ClosureFieldPullbackEquality.overHom_fieldPullbacks_eq_of_algClosed f m
  intro K hK hclosed s
  let C := B.pullback s
  let r := pullback.fst (A.pullback T.hom).scheme.hom s
  let Ls := L.pullback r
  let ms : C.abelian.scheme ⟶ C.dual.abelian.scheme := (Over.pullback s).map m
  let es : (((C.dual.poincareAt ms).tensor
      (Ls.pullback (fst C.abelian.scheme C.abelian.scheme).left)).tensor
      (Ls.pullback (snd C.abelian.scheme C.abelian.scheme).left)).sheaf ≅
        (Ls.pullback μ[C.abelian.scheme].left).sheaf :=
    Rational.DivisorPolarization.inducingFormulaBaseChangeIso D m L em s
  let eGs : Ls.sheaf ≅ (C.graphBundle.tensorPower d).sheaf :=
    (Scheme.Modules.pullback r).mapIso eG ≪≫ B.graphBundle.powerBaseChangeIso r d ≪≫
      (TensorPower.Maps.tensorPowerFunctor _ d).mapIso (B.graphBundle_baseChangeIso s).symm
  obtain ⟨M, ⟨eM⟩⟩ := (Geometric.PolarizationFormula.PolarizedAbelianWithLevel.geometricPullback_normalizedPolarizationFormula B) K s
  have hs : ∀ x y : C.abelian.scheme ⊗ C.abelian.scheme ⟶ C.abelian.scheme,
      C.dual.poincarePairClass (C.abelian.scheme ⊗ C.abelian.scheme)
          (x ≫ C.polarization.isogeny.hom) y =
        C.dual.poincarePairClass (C.abelian.scheme ⊗ C.abelian.scheme)
          (y ≫ C.polarization.isogeny.hom) x :=
    fun x y => Polarization.PairSymmetry.polarizationPairClass_symmetric C.dual C.polarization.isogeny.hom M eM x y
  have hfield : C.abelian.multiplication (2 * d) ≫ C.polarization.isogeny.hom = ms :=
    inducingHom_eq_multiple_of_graphPower_overField C.dual C.polarization.isogeny.hom
      ms Ls d es eGs hs
  change (Over.pullback s).map ((A.pullback T.hom).multiplication (2 * d) ≫ p.isogeny.hom) = ms
  exact ((Over.pullback s).map_comp ((A.pullback T.hom).multiplication (2 * d)) p.isogeny.hom).trans
    ((congrArg (fun a => a ≫ (Over.pullback s).map p.isogeny.hom)
      ((A.pullback T.hom).multiplication_baseChange s (2 * d))).trans hfield)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.InducingHom
