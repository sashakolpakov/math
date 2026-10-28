import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnivariateScalarPullback
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ProductChart

/-! # Product Chart -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ProductChart

noncomputable section

section

/-! The affine-line product over a scalar field has actual open
polynomial charts over every affine chart of its source. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Polynomial

variable {k : Type} [Field k] {Z : Scheme} (f : Z ⟶ Spec (.of k))

def base : Spec (.of k[X]) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))

abbrev space := pullback (base (k := k)) f

def parameter : space f ⟶ Spec (.of k[X]) := pullback.fst _ _

def source : space f ⟶ Z := pullback.snd _ _

variable (U : Z.Opens) (hU : IsAffineOpen U)

def inclusion :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    pullback (base (k := k)) (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, U)))) ⟶ space f := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  exact pullback.map _ _ _ _ (𝟙 _) hU.fromSpec (𝟙 _)
    (by simp) ((Category.comp_id _).trans (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU))

instance inclusion_open :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    IsOpenImmersion (inclusion f U hU) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  unfold inclusion
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstanceAs (IsOpenImmersion (𝟙 (Spec (.of k[X])))))
    (inferInstanceAs (IsOpenImmersion hU.fromSpec)) (by simp)
    (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU)

def chart : Spec (.of Γ(Z, U)[X]) ⟶ space f := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  exact (UnivariateScalarPullback.isPullback (algebraMap k Γ(Z, U))).isoPullback.hom ≫
    inclusion f U hU

instance chart_open : IsOpenImmersion (chart f U hU) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  unfold chart
  infer_instance

theorem chart_parameter :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    chart f U hU ≫ parameter f =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k Γ(Z, U)))) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  rw [chart, parameter, Category.assoc, inclusion, pullback.lift_fst, Category.comp_id]
  exact (UnivariateScalarPullback.isPullback (algebraMap k Γ(Z, U))).isoPullback_hom_fst

theorem chart_source : chart f U hU ≫ source f =
    Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(Z, U) →+* Γ(Z, U)[X])) ≫ hU.fromSpec := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  rw [chart, source, Category.assoc, inclusion, pullback.lift_snd, ← Category.assoc]
  exact congrArg (fun g => g ≫ hU.fromSpec)
    (UnivariateScalarPullback.isPullback (algebraMap k Γ(Z, U))).isoPullback_hom_snd

theorem chart_range : Set.range (chart f U hU) = source f ⁻¹' (U : Set Z) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  change Set.range (inclusion f U hU ∘
    (UnivariateScalarPullback.isPullback (algebraMap k Γ(Z, U))).isoPullback.hom) = _
  rw [Set.range_comp,
    (UnivariateScalarPullback.isPullback (algebraMap k Γ(Z, U))).isoPullback.hom.surjective.range_eq,
    Set.image_univ, inclusion, Scheme.Pullback.range_map]
  have he := congrArg₂ (fun S : Set (Spec (.of k[X])) => fun T : Set Z =>
    pullback.fst (base (k := k)) f ⁻¹' S ∩ pullback.snd (base (k := k)) f ⁻¹' T)
    (show Set.range (𝟙 (Spec (.of k[X]))) = Set.univ from Set.range_id)
    hU.range_fromSpec
  exact he.trans (by rw [Set.preimage_univ, Set.univ_inter]; rfl)

end

/-! Scalar sections of the affine-line product are given on each
native polynomial chart by the ordinary evaluation homomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Polynomial

namespace Section

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ProductChart

theorem evaluation_base {R : Type} [CommRing R] (a : R) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])) = 𝟙 (Spec (.of R)) := by
  rw [← Spec.map_comp]
  have he : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id R := by ext; simp
  change Spec.map (CommRingCat.ofHom ((Polynomial.evalRingHom a).comp Polynomial.C)) = _
  rw [he]
  exact Spec.map_id _

theorem evaluation_naturality {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R) :
    (Polynomial.evalRingHom (f a)).comp (Polynomial.mapRingHom f) =
      f.comp (Polynomial.evalRingHom a) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

variable {k : Type} [Field k] {Z : Scheme} (f : Z ⟶ Spec (.of k))

def sectionMap (a : k) : Z ⟶ space f :=
  pullback.lift (f ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) (𝟙 Z) (by
    rw [Category.assoc, base, evaluation_base, Category.comp_id, Category.id_comp])

theorem section_parameter (a : k) : sectionMap f a ≫ parameter f =
    f ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) := pullback.lift_fst _ _ _

theorem section_source (a : k) : sectionMap f a ≫ source f = 𝟙 Z := pullback.lift_snd _ _ _

theorem chart_section (U : Z.Opens) (hU : IsAffineOpen U) (a : k) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (algebraMap k Γ(Z, U) a))) ≫
      chart f U hU = hU.fromSpec ≫ sectionMap f a := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  apply pullback.hom_ext
  · change (_ ≫ chart f U hU) ≫ parameter f = (_ ≫ sectionMap f a) ≫ parameter f
    rw [Category.assoc, chart_parameter, Category.assoc, section_parameter,
      ← Category.assoc hU.fromSpec, ← Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU]
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
      (evaluation_naturality (algebraMap k Γ(Z, U)) a)
  · change (_ ≫ chart f U hU) ≫ source f = (_ ≫ sectionMap f a) ≫ source f
    rw [Category.assoc, chart_source, ← Category.assoc, evaluation_base,
      Category.id_comp, Category.assoc, section_source, Category.comp_id]

end Section

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ProductChart
