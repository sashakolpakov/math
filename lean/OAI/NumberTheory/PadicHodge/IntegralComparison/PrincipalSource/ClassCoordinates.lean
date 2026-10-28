import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleScalarCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.TopClassLift

/-! # Class Coordinates -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassCoordinates.Scalar

/-! The original nested pushforward has the same ordinary coefficient
coordinate as its source-open supported single-sheaf class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y X Z : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) (N : Y.Modules)
  {m : ℕ} (t : Fin m → Γ(Z,U)) (c : ℕ)

abbrev family := PrincipalPoint.Fraction.family U t
abbrev original := OpenFixedClass.source f i U hU N
abbrev forgetScalars := Principal.AdditiveSections.forgetScalars U

def diagramIso : original f i U hU N ⋙ forgetScalars U ≅
    OpenTopClass.source (f ≫ i) U hU N :=
  OpenScalar.diagramIso f i U hU N ≪≫
    (OpenReindex.pushforwardIso (f ≫ i) U hU N).symm

def coefficientIso :=
  AugmentedCech.TopClassCoefficients.homologyIso (family U t) (forgetScalars U)
    (original f i U hU N) m ≪≫
  homologyMapIso ((AugmentedOrdered.CechFunctor.functor (family U t)).mapIso
    (diagramIso f i U hU N)) m

theorem comparison :
    (SupportedCoordinates.wideIso f i U hU (family U t) N c (m+c)).hom ≫
      (IntrinsicCoordinates.Intrinsic.wideCoordinates (f ≫ i) U hU N t c).hom =
    (forgetScalars U).map (IntegralComparison.Functor.SingleTotal.homologyIso
      (AugmentedOrdered.CechFunctor.functor (family U t)) (original f i U hU N) c m).hom ≫
      (coefficientIso f i U hU N t).hom := by
  have h := congrArg (fun a => a ≫
      (homologyMapIso ((AugmentedOrdered.CechFunctor.functor (family U t)).mapIso
        (OpenReindex.pushforwardIso (f ≫ i) U hU N).symm) m).hom)
    (Supported.SingleScalarCoordinates.comparison (family U t) Γ(Z,U)
      (original f i U hU N) c m (OpenReindex.wideOpens (f ≫ i) U hU) N
      (OpenScalar.diagramIso f i U hU N))
  simp only [SupportedCoordinates.wideIso,
    IntrinsicCoordinates.Intrinsic.wideCoordinates, coefficientIso, diagramIso,
    Iso.trans_hom, homologyMapIso_hom, Functor.mapIso_hom, Functor.map_comp,
    homologyMap_comp, Category.assoc] at h ⊢
  convert h using 1 <;> rfl

theorem topClass (x : (original f i U hU N).obj
    (op (AugmentedOrdered.CechCoordinates.topObject (family U t) m (by simp)))) :
    (coefficientIso f i U hU N t).hom
      (AugmentedOrdered.CechTopClass.topClass (family U t) (original f i U hU N) m (by simp) x) =
    AugmentedCech.TopClassMap.map (family U t)
      (OpenTopClass.source (f ≫ i) U hU N) m (by simp) x := by
  change homologyMap ((AugmentedOrdered.CechFunctor.functor (family U t)).map
    (diagramIso f i U hU N).hom) m
      ((AugmentedCech.TopClassCoefficients.homologyIso (family U t) (forgetScalars U)
        (original f i U hU N) m).hom _) = _
  rw [Augmented.TopClassLift.forget]
  have h := ConcreteCategory.congr_hom
    (AugmentedCech.TopClassMap.naturality (family U t)
      (original f i U hU N ⋙ forgetScalars U) m (by simp) (diagramIso f i U hU N).hom) x
  exact h

end NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassCoordinates.Scalar

namespace NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassCoordinates

/-! A signed original principal class retains its sign and literal
coefficient after the genuine source-open restriction and reindex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y X Z : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) (N : Y.Modules)
  {m : ℕ} (t : Fin m → Γ(Z,U)) (c : ℕ)

abbrev family := PrincipalPoint.Fraction.family U t
abbrev coefficient := OpenFixedClass.source f i U hU N
abbrev total := (IntegralComparison.Functor.SingleTotal.bicomplex
  (AugmentedOrdered.CechFunctor.functor (family U t)) (coefficient f i U hU N) c).total (.up ℕ)

def cast : (ClassCoordinates.total f i U hU N t c).homology (c+m) ⟶ (ClassCoordinates.total f i U hU N t c).homology (m+c) :=
  eqToHom (congrArg (fun q => (ClassCoordinates.total f i U hU N t c).homology q) (Nat.add_comm c m))

abbrev moduleCoordinates := IntegralComparison.Functor.SingleTotal.homologyIso
  (AugmentedOrdered.CechFunctor.functor (family U t)) (coefficient f i U hU N) c m

def wideClass (x : (ClassCoordinates.total f i U hU N t c).homology (c+m)) :=
  (SupportedCoordinates.wideIso f i U hU (family U t) N c (m+c)).hom
    (cast f i U hU N t c x)

variable (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ (f ≫ i) ⁻¹ᵁ U)

def nativeClass (x : (ClassCoordinates.total f i U hU N t c).homology (c+m)) :=
  homologyMap (IntrinsicCoordinates.Intrinsic.sourceMap (f ≫ i) U hU V hV hVU N t c) (m+c)
    (wideClass f i U hU N t c x)

theorem coordinates (x : (ClassCoordinates.total f i U hU N t c).homology (c+m))
    (b : (coefficient f i U hU N).obj
      (op (AugmentedOrdered.CechCoordinates.topObject (family U t) m (by simp))))
    (a : ℤ)
    (h : (moduleCoordinates f i U hU N t c).hom (cast f i U hU N t c x) =
      a • AugmentedOrdered.CechTopClass.topClass (family U t) (coefficient f i U hU N) m (by simp) b) :
    (IntrinsicCoordinates.Intrinsic.nativeCoordinates (f ≫ i) U V hV hVU N t c).hom
      (nativeClass f i U hU N t c V hV hVU x) =
    a • homologyMap (OpenTopClass.complexMap (f ≫ i) U hU V hV hVU N t) m
      (AugmentedCech.TopClassMap.map (family U t)
        (OpenTopClass.source (f ≫ i) U hU N) m (by simp) b) := by
  have hs := ConcreteCategory.congr_hom
    (Scalar.comparison f i U hU N t c)
    (cast f i U hU N t c x)
  change (IntrinsicCoordinates.Intrinsic.wideCoordinates (f ≫ i) U hU N t c).hom
      (wideClass f i U hU N t c x) =
    (Scalar.coefficientIso f i U hU N t).hom
      ((moduleCoordinates f i U hU N t c).hom (cast f i U hU N t c x)) at hs
  have hn := ConcreteCategory.congr_hom
    (IntrinsicCoordinates.Intrinsic.comparison (f ≫ i) U hU V hV hVU N t c)
    (wideClass f i U hU N t c x)
  change (IntrinsicCoordinates.Intrinsic.nativeCoordinates (f ≫ i) U V hV hVU N t c).hom
      (nativeClass f i U hU N t c V hV hVU x) =
    homologyMap (OpenTopClass.complexMap (f ≫ i) U hU V hV hVU N t) m
      ((IntrinsicCoordinates.Intrinsic.wideCoordinates (f ≫ i) U hU N t c).hom
        (wideClass f i U hU N t c x)) at hn
  rw [hs, h, map_zsmul, Scalar.topClass, map_zsmul] at hn
  exact hn

end NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassCoordinates

end

end OAI
