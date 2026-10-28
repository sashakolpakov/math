import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedLift
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Pointed Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PointedLifts

noncomputable section

/-! Arithmetic effectivity for the constructed pointed-lift parameter
scheme. Geometric connectedness and unramifiedness prove that its selected
complex fiber has at most one point, so the actual lift descends to a finite
extension of the specified number field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def fiberParameterPointsEquiv {k : Type u} [Field k] {S : Scheme.{u}}
    (φ : Spec (.of k) ⟶ S) (L : Over S) :
    CountableParameters.ParameterPoints ((Over.pullback φ).obj L) ≃ (Over.mk φ ⟶ L) where
  toFun p := Over.homMk (p.left ≫ pullback.fst L.hom φ) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p.left ≫ ((Over.pullback φ).obj L).hom) ≫ φ = _
    rw [p.w]
    exact Category.id_comp φ)
  invFun a := Over.homMk (pullback.lift a.left (𝟙 _) a.w) (pullback.lift_snd _ _ _)
  left_inv p := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans p.w.symm
  right_inv a := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

namespace PointedLiftParameters

variable {K : Type} [Field K] (κ : K →+* ℂ)
  (X Y Z : Over (Spec (.of K))) (q : Y ⟶ Z) (b : X ⟶ Z)
  (x₀ : ⊤_ (Over (Spec (.of K))) ⟶ X) (y₀ : ⊤_ (Over (Spec (.of K))) ⟶ Y)

abbrev complexTest : Over (Spec (.of K)) := Over.mk (Spec.map (CommRingCat.ofHom κ))

theorem complex_product_connected [GeometricallyConnected X.hom] :
    ConnectedSpace (complexTest κ ⨯ X).left := by
  let T := complexTest κ
  have : Nonempty T.left := ⟨IsLocalRing.closedPoint ℂ⟩
  have : Subsingleton T.left := inferInstanceAs (Subsingleton (Spec (.of ℂ)))
  have : ConnectedSpace (pullback T.hom X.hom : Scheme) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.fst T.hom X.hom)
  exact (Over.prodLeftIsoPullback T X).hom.homeomorph.connectedSpace_iff.mpr inferInstance

variable [GeometricallyConnected X.hom] [FormallyUnramified q.left]
  [LocallyOfFiniteType q.left] [IsSeparated q.left]

include q b x₀ y₀ in
theorem parameters_have_at_most_one_complex_point
    (L : Over (Spec (.of K))) (v : L ⨯ X ⟶ Y)
    (hv : PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ v)
    (hclass : ∀ (T : Over (Spec (.of K))) (f : T ⨯ X ⟶ Y),
      PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ f ↔ ∃! a : T ⟶ L, prod.map a (𝟙 X) ≫ v = f) :
    Subsingleton (CountableParameters.ParameterPoints ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj L)) := by
  have : ConnectedSpace (complexTest κ ⨯ X).left := complex_product_connected κ X
  have : Nonempty (complexTest κ).left := ⟨IsLocalRing.closedPoint ℂ⟩
  let e := fiberParameterPointsEquiv (Spec.map (CommRingCat.ofHom κ)) L
  constructor
  intro p r
  apply e.injective
  let f := prod.map (e p) (𝟙 X) ≫ v
  let g := prod.map (e r) (𝟙 X) ≫ v
  have hf : PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ f :=
    PointedLift.PointedLiftParameters.isPointedLift_restrict X Y Z q b x₀ y₀ (e p) v hv
  have hg : PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ g :=
    PointedLift.PointedLiftParameters.isPointedLift_restrict X Y Z q b x₀ y₀ (e r) v hv
  have hfg : f = g := PointedLift.PointedLiftParameters.unique_on_connected_source X Y Z q b x₀ y₀ f g hf hg
  obtain ⟨a, _, ha⟩ := (hclass (complexTest κ) f).mp hf
  exact (ha (e p) rfl).trans (ha (e r) hfg.symm).symm

variable [NumberField K] (H J : Over (Spec (.of K)))
  (eH : (HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor X Y).RepresentableBy H)
  (eJ : (HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor X Z).RepresentableBy J)
  [IsSeparated Y.hom] [IsSeparated J.hom] [LocallyOfFiniteType H.hom]

include eH eJ in
/-- Construct the arithmetic parameter point of a specified complex pointed
lift, with the required finite extension and extending complex embedding. -/
theorem arithmetic_pointed_lift_parameter
    (f : complexTest κ ⨯ X ⟶ Y) (hf : PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ f)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (L : Over (Spec (.of K))) (j : L ⟶ H), IsClosedImmersion j.left ∧
      ∃ (v : L ⨯ X ⟶ Y), PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ v ∧
        ∃ (B : Base.ArithmeticBaseExtension K κ) (pL : Over.mk B.fieldExtension ⟶ L)
          (c : complexTest κ ⟶ Over.mk B.fieldExtension),
          B.denominator = N ∧ c.left = Spec.map (CommRingCat.ofHom B.embedding) ∧
            prod.map (c ≫ pL) (𝟙 X) ≫ v = f := by
  obtain ⟨L, j, hj, v, hv, hclass⟩ := PointedLift.PointedLiftParameters.exists_pointed_lift_scheme X Y Z q b x₀ y₀ H J eH eJ
  let := hj
  have : LocallyOfFiniteType L.hom := by
    rw [← j.w]
    infer_instance
  obtain ⟨a, ha, _⟩ := (hclass (complexTest κ) f).mp hf
  have := parameters_have_at_most_one_complex_point κ X Y Z q b x₀ y₀ L v hv hclass
  let e := fiberParameterPointsEquiv (Spec.map (CommRingCat.ofHom κ)) L
  let p := e.symm a
  obtain ⟨B, pL, hN', hpL, hfactor⟩ := Parameters.parameter_finite_extension_of_countable_fiber κ L p N hN
  let aL : Over.mk B.fieldExtension ⟶ L := Over.homMk pL hpL
  have he : Spec.map (CommRingCat.ofHom B.embedding) ≫ B.fieldExtension =
      Spec.map (CommRingCat.ofHom κ) := by
    change Spec.map (CommRingCat.ofHom B.embedding) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B.extension.carrier)) = _
    rw [← Spec.map_comp]
    exact congrArg (fun r : K →+* ℂ => Spec.map (CommRingCat.ofHom r)) B.embedding_extends
  let c : complexTest κ ⟶ Over.mk B.fieldExtension :=
    Over.homMk (Spec.map (CommRingCat.ofHom B.embedding)) he
  have hca : c ≫ aL = a := by
    apply Over.OverMorphism.ext
    exact hfactor.trans (congrArg Over.Hom.left (e.apply_symm_apply a))
  exact ⟨L, j, hj, v, hv, B, aL, c, hN', rfl, hca ▸ ha⟩

include eH eJ in
/-- The descended object is an actual scheme map. Its scalar extension is
the originally specified complex lift, and both pointed-lift equations hold
over the constructed finite extension. -/
theorem arithmetic_pointed_lift
    (f : complexTest κ ⨯ X ⟶ Y) (hf : PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ f)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ)
      (fL : Over.mk B.fieldExtension ⨯ X ⟶ Y)
      (c : complexTest κ ⟶ Over.mk B.fieldExtension),
      B.denominator = N ∧ c.left = Spec.map (CommRingCat.ofHom B.embedding) ∧
        PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ fL ∧ prod.map c (𝟙 X) ≫ fL = f := by
  obtain ⟨L, _, _, v, hv, B, aL, c, hBN, hc, hf⟩ :=
    arithmetic_pointed_lift_parameter κ X Y Z q b x₀ y₀ H J eH eJ f hf N hN
  refine ⟨B, prod.map aL (𝟙 X) ≫ v, c, hBN, hc,
    PointedLift.PointedLiftParameters.isPointedLift_restrict X Y Z q b x₀ y₀ aL v hv, ?_⟩
  rw [← Category.assoc, prod.map_map, Category.id_comp]
  exact hf

end PointedLiftParameters

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PointedLifts
