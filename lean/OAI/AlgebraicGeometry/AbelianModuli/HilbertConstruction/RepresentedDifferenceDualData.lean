import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TranslationQuotientLine
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardDescent
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

/-! # Represented Difference Dual Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedDifferenceDualData

noncomputable section

/-! A represented homogeneous Picard sheaf acquires its actual normalized
universal line by descending the original difference bundle along its
translation isogeny. Only the classifying equation at the universal source
point is an input; all test-scheme equations are derived by naturality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardDescent.Construction OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

section IdentityParameter
universe u
variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) {B : Over S}
  (Q : Line.Bundles.LineBundle (B ⊗ A.scheme).left)
  (hQ : A.IsHomogeneousPicardClass B (Line.Bundles.LineBundle.classOf Q))

theorem parameterHomogeneousPicardClass_identity :
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A Q hQ (𝟙 B) =
      (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app
        (.op B) ⟨Line.Bundles.LineBundle.classOf Q, hQ⟩ := by
  apply congrArg ((toSheafify (Scheme.fppfTopology.over S)
    A.homogeneousPicardPresheaf).app (.op B))
  apply Subtype.ext
  change Line.Bundles.LineBundle.pullbackClass ((𝟙 B) ⊗ₘ 𝟙 A.scheme).left
    (Line.Bundles.LineBundle.classOf Q) = Line.Bundles.LineBundle.classOf Q
  rw [id_tensorHom_id]
  exact Line.Bundles.LineBundle.pullbackClass_id _
end IdentityParameter

namespace RepresentedDifferenceDual

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
  (A B : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
  (r : A.homogeneousPicardSheaf.obj.RepresentableBy B.scheme)
  (m : Abelian.Schemes.AbelianScheme.Isogeny A B) [Etale m.hom.left]
  (hHom : A.IsHomogeneousPicardClass A.scheme
    (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)))
  (hm : r.homEquiv m.hom = RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom (𝟙 A.scheme))

include r m hHom hm

omit [IsLocallyNoetherian S] [Etale m.hom.left] in
theorem classifies_points {T : Over S} (a : T ⟶ A.scheme) :
    r.homEquiv (a ≫ m.hom) =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom a := by
  rw [r.homEquiv_comp, hm, RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_naturality,
    Category.comp_id]

omit [IsLocallyNoetherian S] [Etale m.hom.left] in
theorem equal_values {T : Over S} (a b : T ⟶ A.scheme)
    (hab : a ≫ m.hom = b ≫ m.hom) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue b := by
  have h : RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom a =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom b :=
    (classifies_points A B L r m hHom hm a).symm.trans
      ((congrArg r.homEquiv hab).trans (classifies_points A B L r m hHom hm b))
  exact (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom a).symm.trans
    ((congrArg (A.homogeneousPicardSheafInclusion.hom.app (.op T)) h).trans
      (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom b))

local instance product_locallyNoetherian : IsLocallyNoetherian (B.scheme ⊗ A.scheme).left :=
  Picard.PoincareBundle.Product.Noetherian.product_noetherian B.scheme A.scheme

local instance product_affine : IsAffineHom (m.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : IsAffineHom (Over.Hom.left (𝟙 A.scheme)) :=
    inferInstanceAs (IsAffineHom (𝟙 A.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorAffine m.hom (𝟙 A.scheme)

local instance product_flat : Flat (m.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : Flat (Over.Hom.left (𝟙 A.scheme)) := inferInstanceAs (Flat (𝟙 A.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorFlat m.hom (𝟙 A.scheme)

local instance product_surjective : Surjective (m.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : Surjective (Over.Hom.left (𝟙 A.scheme)) :=
    inferInstanceAs (Surjective (𝟙 A.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.tensorSurjective m.hom (𝟙 A.scheme)

local instance product_finitelyPresented :
    LocallyOfFinitePresentation (m.hom ⊗ₘ 𝟙 A.scheme).left := by
  let : LocallyOfFinitePresentation (Over.Hom.left (𝟙 A.scheme)) :=
    inferInstanceAs (LocallyOfFinitePresentation (𝟙 A.scheme.left))
  exact Picard.PoincareBundle.Product.Covers.property_tensor (@LocallyOfFinitePresentation) m.hom
    (𝟙 A.scheme) inferInstance inferInstance

def line : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A.scheme B.scheme :=
  (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).rigidifiedQuotientLine m.hom
    (fun {_T} _ a b hab => equal_values A B L r m hHom hm a b hab)

def recovery :
    (((line A B L r m hHom hm).bundle).pullback (m.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf :=
  (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).normalizedQuotientLinePullbackIso m.hom
    (fun {_T} _ a b hab => equal_values A B L r m hHom hm a b hab)

theorem recovery_class :
    Line.Bundles.LineBundle.pullbackClass (m.hom ⊗ₘ 𝟙 A.scheme).left
        (Line.Bundles.LineBundle.classOf (line A B L r m hHom hm).bundle) =
      Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) :=
  Quotient.sound ⟨recovery A B L r m hHom hm⟩

theorem homogeneous :
    A.IsHomogeneousPicardClass B.scheme
      (Line.Bundles.LineBundle.classOf (line A B L r m hHom hm).bundle) := by
  apply AbelianScheme.IsogenyQuotient.HomogeneousPicardDescent.Construction.homogeneousPicardClass_of_fppf_pullback A.scheme m.hom
  change A.IsHomogeneousPicardClass A.scheme
    (Line.Bundles.LineBundle.pullbackClass (m.hom ⊗ₘ 𝟙 A.scheme).left
      (Line.Bundles.LineBundle.classOf (line A B L r m hHom hm).bundle))
  exact (congrArg (A.IsHomogeneousPicardClass A.scheme)
    (recovery_class A B L r m hHom hm)).mpr hHom

def secondAxis :
    (((line A B L r m hHom hm).bundle).pullback
      (lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme)).left).sheaf ≅
        Line.Bundles.structureModule A.scheme.left := by
  have hwOver : lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme) ≫
      (m.hom ⊗ₘ 𝟙 A.scheme) = lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme) := by
    rw [lift_map, MonObj.one_comp, Category.id_comp]
  have hw : (lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme)).left ≫
      (m.hom ⊗ₘ 𝟙 A.scheme).left =
        (lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme)).left :=
    congrArg Over.Hom.left hwOver
  have hc : Line.Bundles.LineBundle.pullbackClass
      (lift (1 : A.scheme ⟶ B.scheme) (𝟙 A.scheme)).left
      (Line.Bundles.LineBundle.classOf (line A B L r m hHom hm).bundle) =
      Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.trivial A.scheme.left) :=
    (congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f
      (Line.Bundles.LineBundle.classOf (line A B L r m hHom hm).bundle)) hw.symm).trans
      ((Line.Bundles.LineBundle.pullbackClass_comp
        (lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme)).left (m.hom ⊗ₘ 𝟙 A.scheme).left _).trans
        ((congrArg (Line.Bundles.LineBundle.pullbackClass (lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme)).left)
          (recovery_class A B L r m hHom hm)).trans
          (Quotient.sound (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle_normalized_right A L))))
  exact (Quotient.exact hc).some

theorem universalClass :
    r.homEquiv (𝟙 B.scheme) =
      (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app
        (.op B.scheme) ⟨Line.Bundles.LineBundle.classOf (line A B L r m hHom hm).bundle,
          homogeneous A B L r m hHom hm⟩ := by
  let c : A.homogeneousPicardPresheaf.obj (.op B.scheme) :=
    ⟨Line.Bundles.LineBundle.classOf (line A B L r m hHom hm).bundle, homogeneous A B L r m hHom hm⟩
  let δ : A.homogeneousPicardPresheaf.obj (.op A.scheme) :=
    ⟨Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L), hHom⟩
  let sheafMap := toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf
  have hc : A.homogeneousPicardPresheaf.map m.hom.op c = δ := by
    apply Subtype.ext
    exact recovery_class A B L r m hHom hm
  apply AbelianScheme.IsogenyQuotient.FppfSheafRestriction.Construction.fppfSheaf_restriction_injective m.hom A.homogeneousPicardSheaf
  have h₀ : A.homogeneousPicardSheaf.obj.map m.hom.op (r.homEquiv (𝟙 B.scheme)) =
      r.homEquiv m.hom :=
      (r.homEquiv_comp m.hom (𝟙 B.scheme)).symm.trans
        (congrArg r.homEquiv (Category.comp_id m.hom))
  have h₁ : r.homEquiv m.hom = sheafMap.app (.op A.scheme) δ :=
    hm.trans (parameterHomogeneousPicardClass_identity A _ hHom)
  have h₂ : sheafMap.app (.op A.scheme) δ =
      A.homogeneousPicardSheaf.obj.map m.hom.op (sheafMap.app (.op B.scheme) c) :=
    (congrArg (sheafMap.app (.op A.scheme)) hc.symm).trans
      (sheafMap.naturality_apply m.hom.op c)
  exact h₀.trans (h₁.trans h₂)

theorem pointClass {T : Over S} (a : T ⟶ B.scheme) :
    r.homEquiv a = RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A
      (line A B L r m hHom hm).bundle (homogeneous A B L r m hHom hm) a := by
  rw [r.homEquiv_eq, RepresentedDifferenceDual.universalClass A B L r m hHom hm,
    ← parameterHomogeneousPicardClass_identity,
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_naturality, Category.comp_id]

def dualData : Dual.Data.DualAbelianData A where
  abelian := B
  representable := r
  origin T := (pointClass A B L r m hHom hm (1 : T ⟶ B.scheme)).trans
    (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_one A (line A B L r m hHom hm).bundle
      (homogeneous A B L r m hHom hm) (secondAxis A B L r m hHom hm) T)
  poincare := (line A B L r m hHom hm).bundle
  poincareHomogeneous := homogeneous A B L r m hHom hm
  universalClass := RepresentedDifferenceDual.universalClass A B L r m hHom hm
  normalizedAtAbelianZero := ⟨(line A B L r m hHom hm).axis⟩
  normalizedAtDualZero := ⟨secondAxis A B L r m hHom hm⟩

end RepresentedDifferenceDual

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedDifferenceDualData
