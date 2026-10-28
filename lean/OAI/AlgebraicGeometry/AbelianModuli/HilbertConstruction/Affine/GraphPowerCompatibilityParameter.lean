import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolarizationGraphPower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Graph Power Compatibility Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GraphPowerCompatibilityParameter.AffineRawGraphPower

noncomputable section

/-! The actual graph-power comparison locus over any affine Noetherian
base. The native projective rigidified-frame scheme classifies the
comparison on every test scheme, without positivity, type, or level data. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {g : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (D : Dual.Data.DualAbelianData A)
variable (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
variable (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left) (d : ℕ)

def differenceBundle : Line.Bundles.LineBundle A.scheme.left :=
  (A.zeroNormalizedBundle L).tensor
    ((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d).reciprocalFrameBundle

omit [IsMonHom p] in
theorem differenceBundle_class :
    Line.Bundles.LineBundle.classOf (differenceBundle A D p L d) =
      Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle L) *
        (Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d))⁻¹ := by
  rw [differenceBundle, Line.Bundles.LineBundle.classOf_tensor, Line.Bundles.LineBundle.classOf_reciprocalFrameBundle]

def differenceBundle_zeroIso :
    ((differenceBundle A D p L d).pullback η[A.scheme].left).sheaf ≅
      Line.Bundles.structureModule S := by
  have hL : Line.Bundles.LineBundle.pullbackClass η[A.scheme].left
      (Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle L)) = 1 :=
    Quotient.sound ⟨A.zeroNormalizedBundle_zeroIso L⟩
  have hz : (Line.Bundles.LineBundle.pullbackClassMonoidHom η[A.scheme].left)
      (Line.Bundles.LineBundle.classOf (PoincareGraph.Bundles.poincareGraphBundle D p)) = 1 :=
    Quotient.sound ⟨PoincareGraph.Fibers.poincareGraphBundle_zeroIso D p⟩
  have hzpow : Line.Bundles.LineBundle.pullbackClass η[A.scheme].left
      (Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d)) = 1 := by
    rw [Line.Bundles.LineBundle.classOf_tensorPower]
    change (Line.Bundles.LineBundle.pullbackClassMonoidHom η[A.scheme].left)
      (Line.Bundles.LineBundle.classOf (PoincareGraph.Bundles.poincareGraphBundle D p) ^ d) = 1
    rw [map_pow, hz, one_pow]
  have h : Line.Bundles.LineBundle.classOf ((differenceBundle A D p L d).pullback η[A.scheme].left) = 1 := by
    change Line.Bundles.LineBundle.pullbackClass η[A.scheme].left
      (Line.Bundles.LineBundle.classOf (differenceBundle A D p L d)) = 1
    rw [differenceBundle_class A D p L d]
    change (Line.Bundles.LineBundle.pullbackClassMonoidHom η[A.scheme].left) (_ * _⁻¹) = 1
    rw [map_mul, map_inv]
    change Line.Bundles.LineBundle.pullbackClass η[A.scheme].left
      (Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle L)) *
        (Line.Bundles.LineBundle.pullbackClass η[A.scheme].left
          (Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d)))⁻¹ = 1
    rw [hL, hzpow, inv_one, mul_one]
  exact Classical.choice (Quotient.exact h)

omit [IsMonHom p] in
theorem differenceBundle_trivial_iff {Y : Scheme.{u}} (f : Y ⟶ A.scheme.left) :
    Nonempty (Line.Bundles.structureModule Y ≅ ((differenceBundle A D p L d).pullback f).sheaf) ↔
      Nonempty (((A.zeroNormalizedBundle L).pullback f).sheaf ≅
        (((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d).pullback f).sheaf) := by
  have hc : Line.Bundles.LineBundle.classOf ((differenceBundle A D p L d).pullback f) =
      Line.Bundles.LineBundle.classOf ((A.zeroNormalizedBundle L).pullback f) *
        (Line.Bundles.LineBundle.classOf (((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d).pullback f))⁻¹ := by
    change Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf (differenceBundle A D p L d)) = _
    rw [differenceBundle_class A D p L d]
    change (Line.Bundles.LineBundle.pullbackClassMonoidHom f) (_ * _⁻¹) = _
    rw [map_mul, map_inv]
    rfl
  constructor
  · rintro ⟨e⟩
    have h : Line.Bundles.LineBundle.classOf ((differenceBundle A D p L d).pullback f) = 1 :=
      Quotient.sound ⟨e.symm⟩
    rw [hc, mul_inv_eq_one] at h
    exact Quotient.exact h
  · intro he
    have h : Line.Bundles.LineBundle.classOf ((A.zeroNormalizedBundle L).pullback f) =
        Line.Bundles.LineBundle.classOf (((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d).pullback f) := Quotient.sound he
    have hq : Line.Bundles.LineBundle.classOf ((differenceBundle A D p L d).pullback f) = 1 := by
      rw [hc, h, mul_inv_cancel]
    exact ⟨(Classical.choice (Quotient.exact hq)).symm⟩

def powerBaseChangeIso {T : Scheme.{u}} (b : T ⟶ S) :
    (((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d).pullback
      (pullback.fst A.scheme.hom b)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback b) ((Over.pullback b).map p)).tensorPower d).sheaf :=
  (PoincareGraph.Bundles.poincareGraphBundle D p).powerBaseChangeIso (pullback.fst A.scheme.hom b) d ≪≫
    (TensorPower.Maps.tensorPowerFunctor _ d).mapIso (PoincareGraph.Bundles.poincareGraphBundle_baseChangeIso D p b).symm

variable [IsAffine S] [IsLocallyNoetherian S]

local instance affineGraphPower_noetherianSections : IsNoetherianRing Γ(S, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩

def parameter : Over S :=
  FormalGeometry.Completion.Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme A.scheme P
    (differenceBundle A D p L d) η[A.scheme].left η[A.scheme].w
    (differenceBundle_zeroIso A D p L d)

instance parameter_locallyOfFiniteType : LocallyOfFiniteType (parameter A D p P L d).hom :=
  FormalGeometry.Completion.Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme_locallyOfFiniteType A.scheme P
    (differenceBundle A D p L d) η[A.scheme].left η[A.scheme].w
    (differenceBundle_zeroIso A D p L d)

instance parameter_quasiCompact : QuasiCompact (parameter A D p P L d).hom :=
  FormalGeometry.Completion.Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme_quasiCompact A.scheme P
    (differenceBundle A D p L d) η[A.scheme].left η[A.scheme].w
    (differenceBundle_zeroIso A D p L d)

instance parameter_mono : Mono (parameter A D p P L d).hom :=
  Picard.ThetaConstruction.RelativeFrameClassification.Geometric.relativeProjective_projectiveRigidifiedFrame_mono P
    η[A.scheme].left η[A.scheme].w (differenceBundle_zeroIso A D p L d)

theorem parameter_cartesian_hasPoint_iff
    {Y T : Scheme.{u}} (f : Y ⟶ A.scheme.left) (ρ : Y ⟶ T)
    (b : T ⟶ S) (hp : IsPullback f ρ A.scheme.hom b) :
    Nonempty (Over.mk b ⟶ parameter A D p P L d) ↔
      Nonempty (((A.zeroNormalizedBundle L).pullback f).sheaf ≅
        (((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d).pullback f).sheaf) := by
  have h := Picard.ThetaConstruction.RelativeFrameClassification.Geometric.relativeProjective_projectiveRigidifiedFrame_hasPoint_iff_trivialClass
    P η[A.scheme].left η[A.scheme].w (differenceBundle_zeroIso A D p L d) f ρ b hp
  refine h.trans ?_
  constructor
  · intro hc
    exact (differenceBundle_trivial_iff A D p L d f).mp
      ⟨(Classical.choice (Quotient.exact hc)).symm⟩
  · intro hc
    obtain ⟨e⟩ := (differenceBundle_trivial_iff A D p L d f).mpr hc
    exact Quotient.sound ⟨e.symm⟩

theorem parameter_hasPoint_iff (T : Over S) :
    Nonempty (T ⟶ parameter A D p P L d) ↔
      Nonempty (((A.zeroNormalizedBundle L).pullback
        (pullback.fst A.scheme.hom T.hom)).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom)
          ((Over.pullback T.hom).map p)).tensorPower d).sheaf) := by
  have h := parameter_cartesian_hasPoint_iff A D p P L d
    (pullback.fst A.scheme.hom T.hom) (pullback.snd A.scheme.hom T.hom)
    T.hom (IsPullback.of_hasPullback A.scheme.hom T.hom)
  constructor
  · intro hp
    exact ⟨Classical.choice (h.mp hp) ≪≫ AffineRawGraphPower.powerBaseChangeIso A D p d T.hom⟩
  · rintro ⟨e⟩
    exact h.mpr ⟨e ≪≫ (AffineRawGraphPower.powerBaseChangeIso A D p d T.hom).symm⟩

def parameterPointEquiv (T : Over S) :
    (T ⟶ parameter A D p P L d) ≃
      PLift (Nonempty (((A.zeroNormalizedBundle L).pullback
        (pullback.fst A.scheme.hom T.hom)).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom)
          ((Over.pullback T.hom).map p)).tensorPower d).sheaf)) where
  toFun f := ⟨(parameter_hasPoint_iff A D p P L d T).mp ⟨f⟩⟩
  invFun h := Classical.choice ((parameter_hasPoint_iff A D p P L d T).mpr h.down)
  left_inv f := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (parameter A D p P L d).hom).mp
    exact Over.w _ |>.trans f.w.symm
  right_inv _ := Subsingleton.elim _ _

def universalIso :
    ((A.zeroNormalizedBundle L).pullback
      (pullback.fst A.scheme.hom (parameter A D p P L d).hom)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback (parameter A D p P L d).hom)
        ((Over.pullback (parameter A D p P L d).hom).map p)).tensorPower d).sheaf :=
  Classical.choice ((parameter_hasPoint_iff A D p P L d (parameter A D p P L d)).mp ⟨𝟙 _⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GraphPowerCompatibilityParameter.AffineRawGraphPower
