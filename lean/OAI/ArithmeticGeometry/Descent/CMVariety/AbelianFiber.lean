import OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence
import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety

/-! # Abelian Fiber -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AbelianFiber

noncomputable section

/-!
Descent of actual abelian fibers from arithmetic parameter points.
The model below is a smooth proper geometrically connected commutative
group scheme, with a group-preserving complex base-change isomorphism.
No model of a CM abelian variety is assumed or postulated.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The exact number-field-model conclusion from the CMAbelianVariety specification. -/
def HasNumberFieldModel (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Prop :=
  ∃ (K : Subfield ℂ), NumberField K ∧
    ∃ (B : Over (Spec (CommRingCat.of K))) (groupB : GrpObj B),
      letI := groupB
      Smooth B.hom ∧ IsProper B.hom ∧ GeometricallyConnected B.hom ∧
      IsCommMonObj B ∧
      let F := Over.pullback (Spec.map (CommRingCat.ofHom K.subtype))
      letI : GrpObj (F.obj B) := Functor.grpObjObj (F := F)
      ∃ e : F.obj B ≅ A.toOver, IsMonHom e.hom

/-- If a parameter point is defined over a number field, the actual
abelian fiber is defined over that field, including its group law. -/
theorem abelian_fiber_descends_of_parameter_descends
    {S : Scheme} {g : ℕ} (U : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : (U.pullback p).scheme ≅ A.toOver) [IsMonHom e.hom]
    (hp : ∃ (K : Subfield ℂ), NumberField K ∧
      ∃ pK : Spec (CommRingCat.of K) ⟶ S,
        Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p) :
    HasNumberFieldModel A := by
  obtain ⟨K, hK, pK, rfl⟩ := hp
  let B := U.pullback pK
  let ι := Spec.map (CommRingCat.ofHom K.subtype)
  let c := (U.pullbackCompIso pK ι).symm ≪≫ e
  refine ⟨K, hK, B.scheme, B.group, ?_⟩
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, c, ?_⟩
  exact inferInstanceAs (IsMonHom ((U.pullbackCompIso pK ι).inv ≫ e.hom))

/-- An isolated point of an arithmetic parameter space gives a number-field
model of its abelian fiber. Both the parameter descent and the group-law
compatibility of the fiber comparison are proved. -/
theorem abelian_fiber_descends_of_isolated_parameter
    {S : Scheme} {g : ℕ} (f : S ⟶ Spec (CommRingCat.of ℚ))
    [LocallyOfFiniteType f] (U : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) (hp : IsOpen {p (IsLocalRing.closedPoint ℂ)})
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (e : (U.pullback p).scheme ≅ A.toOver)
    [IsMonHom e.hom] : HasNumberFieldModel A :=
  abelian_fiber_descends_of_parameter_descends U p A e
    (AlgebraicPoints.Abelian.complex_point_descends_of_isolated f p hp)

/-- The same descent applies when isolation is established after extension
of the arithmetic parameter space to ℂ. -/
theorem abelian_fiber_descends_of_geometrically_isolated_parameter
    {S : Scheme} {g : ℕ} (f : S ⟶ Spec (CommRingCat.of ℚ))
    [LocallyOfFiniteType f] (U : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ CategoryTheory.Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
    (hp : IsOpen {p (IsLocalRing.closedPoint ℂ)})
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : (U.pullback (p ≫ CategoryTheory.Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))).scheme ≅ A.toOver)
    [IsMonHom e.hom] : HasNumberFieldModel A :=
  abelian_fiber_descends_of_parameter_descends U _ A e
    (AlgebraicPoints.Abelian.complex_point_descends_of_isolated_baseChange f p hp)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AbelianFiber
