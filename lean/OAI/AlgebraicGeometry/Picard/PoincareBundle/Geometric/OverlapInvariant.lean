import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.OverlapInvariant
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionInvariant
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantCongr
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapImage
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsoDescent

/-! # Overlap Invariant -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapInvariant

noncomputable section

/-!
# The actual geometric invariant sheaf is unchanged by an isomorphic overlap presentation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

/-- Compose three canonical comparison squares using an equality of whole invariant isomorphisms. -/
theorem comparison_paste {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' D' : C} {M : D} (e : A ≅ D') (e₁ : A ≅ B) (e₂ : B ≅ C') (e₃ : C' ≅ D')
    (a : F.obj A ⟶ M) (b : F.obj B ⟶ M) (c : F.obj C' ⟶ M) (d : F.obj D' ⟶ M)
    (he : e = e₁ ≪≫ e₂ ≪≫ e₃)
    (h₁ : F.map e₁.hom ≫ b = a) (h₂ : F.map e₂.hom ≫ c = b) (h₃ : F.map e₃.hom ≫ d = c) :
    F.map e.hom ≫ d = a := by
  subst e
  simp only [Iso.trans_hom, F.map_comp, Category.assoc]
  rw [h₃, h₂, h₁]

end

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapImage OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapGluing

variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X)
  (h : p ≫ f = q ≫ f) (r : W ⟶ Z) (M : X.Modules)
  (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)

/-- The invariant with standard composite projection adjunctions and transported comparison data. -/
def changedInvariant : Y.Modules :=
  AdjointCechInvariant.invariants (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ p))
    (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ q))
    (OverlapImage.compositeDirectImageIso f p q h r)
    (Cech.AdjunctionChange.changedGluing (Scheme.Modules.pullbackComp r p)
      (Scheme.Modules.pullbackComp r q) ((Scheme.Modules.pullback r).map σ.hom))

/-- The invariant before replacing composite adjunctions by the standard geometric ones. -/
def extendedInvariant : Y.Modules :=
  AdjointCechInvariant.invariants ((Scheme.Modules.pullbackPushforwardAdjunction p).comp
      (Scheme.Modules.pullbackPushforwardAdjunction r))
    ((Scheme.Modules.pullbackPushforwardAdjunction q).comp
      (Scheme.Modules.pullbackPushforwardAdjunction r))
    (Cech.OverlapExtension.extendedRightIso
      (CechInvariant.directImageIso f p q h) (K := Scheme.Modules.pushforward r))
    ((Scheme.Modules.pullback r).map σ.hom)

def changedComparison : (Scheme.Modules.pullback f).obj (changedInvariant f p q h r M σ) ⟶ M :=
  AdjointCechInvariant.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ p))
    (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ q)) (OverlapImage.compositeDirectImageIso f p q h r)
    (Cech.AdjunctionChange.changedGluing (Scheme.Modules.pullbackComp r p)
      (Scheme.Modules.pullbackComp r q) ((Scheme.Modules.pullback r).map σ.hom))

def extendedComparison : (Scheme.Modules.pullback f).obj (extendedInvariant f p q h r M σ) ⟶ M :=
  AdjointCechInvariant.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).comp (Scheme.Modules.pullbackPushforwardAdjunction r))
    ((Scheme.Modules.pullbackPushforwardAdjunction q).comp (Scheme.Modules.pullbackPushforwardAdjunction r))
    (Cech.OverlapExtension.extendedRightIso
      (CechInvariant.directImageIso f p q h) (K := Scheme.Modules.pushforward r))
    ((Scheme.Modules.pullback r).map σ.hom)

/-- Identifying the right-image and gluing data retains the actual invariant object. -/
def coordinateInvariantIso :
    CechInvariant.invariantSheaf f (r ≫ p) (r ≫ q) (OverlapImage.liftedRelation f p q h r) M
      (OverlapGluing.extendedGluing p q r M σ) ≅ changedInvariant f p q h r M σ :=
  Cech.InvariantCongr.invariantIso (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ p))
    (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ q))
    (OverlapImage.compositeDirectImageIso_eq f p q h r).symm (OverlapGluing.extendedGluing_hasChangedHom p q r M σ)

theorem coordinateComparison_fac :
    (Scheme.Modules.pullback f).map (coordinateInvariantIso f p q h r M σ).hom ≫
      changedComparison f p q h r M σ =
    CechInvariant.comparison f (r ≫ p) (r ≫ q) (OverlapImage.liftedRelation f p q h r) M
      (OverlapGluing.extendedGluing p q r M σ) :=
  Cech.InvariantCongr.comparison_fac (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ p))
    (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ q))
    (OverlapImage.compositeDirectImageIso_eq f p q h r).symm (OverlapGluing.extendedGluing_hasChangedHom p q r M σ)

/-- Canonical mate comparisons identify the two choices of geometric projection adjunctions. -/
def adjunctionInvariantIso : changedInvariant f p q h r M σ ≅ extendedInvariant f p q h r M σ :=
  Cech.AdjunctionInvariant.invariantIso
    ((Scheme.Modules.pullbackPushforwardAdjunction p).comp (Scheme.Modules.pullbackPushforwardAdjunction r))
    (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ p))
    ((Scheme.Modules.pullbackPushforwardAdjunction q).comp (Scheme.Modules.pullbackPushforwardAdjunction r))
    (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ q))
    (Scheme.Modules.pullbackComp r p) (Scheme.Modules.pullbackComp r q)
    (Scheme.Modules.pushforwardComp r p) (Scheme.Modules.pushforwardComp r q)
    (Scheme.Modules.conjugateEquiv_pullbackComp_inv r p)
    (Scheme.Modules.conjugateEquiv_pullbackComp_inv r q)
    (Cech.OverlapExtension.extendedRightIso
      (CechInvariant.directImageIso f p q h) (K := Scheme.Modules.pushforward r))
    ((Scheme.Modules.pullback r).map σ.hom)

theorem adjunctionComparison_fac :
    (Scheme.Modules.pullback f).map (adjunctionInvariantIso f p q h r M σ).hom ≫
      extendedComparison f p q h r M σ = changedComparison f p q h r M σ :=
  Cech.AdjunctionInvariant.comparison_commutes
    ((Scheme.Modules.pullbackPushforwardAdjunction p).comp (Scheme.Modules.pullbackPushforwardAdjunction r))
    (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ p))
    ((Scheme.Modules.pullbackPushforwardAdjunction q).comp (Scheme.Modules.pullbackPushforwardAdjunction r))
    (Scheme.Modules.pullbackPushforwardAdjunction (r ≫ q))
    (Scheme.Modules.pullbackComp r p) (Scheme.Modules.pullbackComp r q)
    (Scheme.Modules.pushforwardComp r p) (Scheme.Modules.pushforwardComp r q)
    (Scheme.Modules.conjugateEquiv_pullbackComp_inv r p)
    (Scheme.Modules.conjugateEquiv_pullbackComp_inv r q)
    (Cech.OverlapExtension.extendedRightIso
      (CechInvariant.directImageIso f p q h) (K := Scheme.Modules.pushforward r))
    ((Scheme.Modules.pullback r).map σ.hom) (Scheme.Modules.pullbackPushforwardAdjunction f)

variable [IsIso r]

/-- An isomorphic overlap gives a fully faithful pullback functor, so extension retains invariants. -/
def extensionInvariantIso : extendedInvariant f p q h r M σ ≅
    CechInvariant.invariantSheaf f p q h M σ := by
  have : (Scheme.Modules.pullback r).IsEquivalence := IsoDescent.pullback_isEquivalence (asIso r)
  exact Cech.OverlapInvariant.invariantIso (Scheme.Modules.pullbackPushforwardAdjunction p)
    (Scheme.Modules.pullbackPushforwardAdjunction q) (CechInvariant.directImageIso f p q h)
    (Scheme.Modules.pullbackPushforwardAdjunction r) σ.hom

theorem extensionComparison_fac :
    (Scheme.Modules.pullback f).map (extensionInvariantIso f p q h r M σ).hom ≫
      CechInvariant.comparison f p q h M σ = extendedComparison f p q h r M σ := by
  have : (Scheme.Modules.pullback r).IsEquivalence := IsoDescent.pullback_isEquivalence (asIso r)
  exact Cech.OverlapInvariant.comparison_commutes (Scheme.Modules.pullbackPushforwardAdjunction p)
    (Scheme.Modules.pullbackPushforwardAdjunction q) (CechInvariant.directImageIso f p q h)
    (Scheme.Modules.pullbackPushforwardAdjunction r) σ.hom (Scheme.Modules.pullbackPushforwardAdjunction f)

/-- The actual geometric Čech invariant is independent of the chosen isomorphic overlap scheme. -/
def invariantIso :
    CechInvariant.invariantSheaf f (r ≫ p) (r ≫ q) (OverlapImage.liftedRelation f p q h r) M
      (OverlapGluing.extendedGluing p q r M σ) ≅ CechInvariant.invariantSheaf f p q h M σ :=
  coordinateInvariantIso f p q h r M σ ≪≫ adjunctionInvariantIso f p q h r M σ ≪≫
    extensionInvariantIso f p q h r M σ

/-- Its canonical isomorphism also retains the actual pullback comparison. -/
theorem comparison_commutes :
    (Scheme.Modules.pullback f).map (invariantIso f p q h r M σ).hom ≫
      CechInvariant.comparison f p q h M σ =
    CechInvariant.comparison f (r ≫ p) (r ≫ q) (OverlapImage.liftedRelation f p q h r) M
      (OverlapGluing.extendedGluing p q r M σ) :=
  comparison_paste (Scheme.Modules.pullback f) (invariantIso f p q h r M σ)
    (coordinateInvariantIso f p q h r M σ) (adjunctionInvariantIso f p q h r M σ)
    (extensionInvariantIso f p q h r M σ) _ (changedComparison f p q h r M σ)
    (extendedComparison f p q h r M σ) _ rfl
    (coordinateComparison_fac f p q h r M σ) (adjunctionComparison_fac f p q h r M σ)
    (extensionComparison_fac f p q h r M σ)

/-- Invertibility of the actual invariant comparison is unchanged by an isomorphic overlap scheme. -/
theorem comparison_isIso_iff :
    IsIso (CechInvariant.comparison f (r ≫ p) (r ≫ q) (OverlapImage.liftedRelation f p q h r) M
      (OverlapGluing.extendedGluing p q r M σ)) ↔ IsIso (CechInvariant.comparison f p q h M σ) := by
  rw [← comparison_commutes f p q h r M σ]
  exact isIso_comp_left_iff _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapInvariant
