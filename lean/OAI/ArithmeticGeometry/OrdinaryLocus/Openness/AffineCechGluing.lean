import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCech
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Affine Cech Gluing -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCechGluing.Construction

noncomputable section

/-! Gluing and functoriality for Čech cochains of affine sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v

variable (R : CommRingCat.{u})
    (F : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of (PrimeSpectrum R)))
    {ι : Type v} (f : ι → R)

theorem affinePair_restriction_eq_iff
    {U V W : TopologicalSpace.Opens (PrimeSpectrum R)} (hW : W = U ⊓ V)
    (hU : W ≤ U) (hV : W ≤ V) (x : F.obj.obj (op U)) (y : F.obj.obj (op V)) :
    F.obj.map (homOfLE hU).op x = F.obj.map (homOfLE hV).op y ↔
      F.obj.map (U.infLELeft V).op x = F.obj.map (U.infLERight V).op y := by
  subst W
  rfl

theorem affineCechD0_eq_zero_iff (x : AffineCech.Construction.affineCechC0 R F f) :
    AffineCech.Construction.affineCechD0 R F f x = 0 ↔
      TopCat.Presheaf.IsCompatible F.obj (fun i ↦ PrimeSpectrum.basicOpen (f i)) x := by
  constructor
  · intro hx i j
    have h := congrFun (congrFun hx i) j
    change AffineSectionCoordinates.Construction.affineBasicSectionRestriction R F (f j) (f i * f j) (dvd_mul_left _ _) (x j) -
      AffineSectionCoordinates.Construction.affineBasicSectionRestriction R F (f i) (f i * f j) (dvd_mul_right _ _) (x i) = 0 at h
    have h' := (sub_eq_zero.mp h).symm
    exact (affinePair_restriction_eq_iff R F (PrimeSpectrum.basicOpen_mul _ _)
      (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R _ _ (dvd_mul_right _ _))
      (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R _ _ (dvd_mul_left _ _)) (x i) (x j)).mp h'
  · intro hx
    funext i j
    change AffineSectionCoordinates.Construction.affineBasicSectionRestriction R F (f j) (f i * f j) (dvd_mul_left _ _) (x j) -
      AffineSectionCoordinates.Construction.affineBasicSectionRestriction R F (f i) (f i * f j) (dvd_mul_right _ _) (x i) = 0
    apply sub_eq_zero.mpr
    exact ((affinePair_restriction_eq_iff R F (PrimeSpectrum.basicOpen_mul _ _)
      (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R _ _ (dvd_mul_right _ _))
      (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R _ _ (dvd_mul_left _ _)) (x i) (x j)).mpr (hx i j)).symm

theorem affineCech_sections_glue (hf : Ideal.span (Set.range f) = ⊤)
    (x : AffineCech.Construction.affineCechC0 R F f) (hx : AffineCech.Construction.affineCechD0 R F f x = 0) :
    ∃! m : F.obj.obj (op ⊤), ∀ i, F.obj.map (PrimeSpectrum.basicOpen (f i)).leTop.op m = x i := by
  exact F.existsUnique_gluing' (fun i ↦ PrimeSpectrum.basicOpen (f i)) ⊤
    (fun _ ↦ homOfLE le_top)
    (by rw [(PrimeSpectrum.iSup_basicOpen_eq_top_iff).mpr hf]) x
    ((affineCechD0_eq_zero_iff R F f x).mp hx)

theorem affineCechD1_comp_D0_unconditional : AffineCech.Construction.affineCechD1 R F f ∘ₗ AffineCech.Construction.affineCechD0 R F f = 0 := by
  apply LinearMap.ext
  intro x
  funext i j k
  simp [AffineCech.Construction.affineCechD0, AffineCech.Construction.affineCechD1, AffineSectionCoordinates.Construction.affineBasicSectionRestriction_comp_apply R F]

variable {G : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of (PrimeSpectrum R))} (φ : F ⟶ G)

def affineCechMap0 : AffineCech.Construction.affineCechC0 R F f →ₗ[R] AffineCech.Construction.affineCechC0 R G f :=
  LinearMap.pi fun i ↦ (φ.hom.app _).hom ∘ₗ LinearMap.proj i

def affineCechMap1 : AffineCech.Construction.affineCechC1 R F f →ₗ[R] AffineCech.Construction.affineCechC1 R G f :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (φ.hom.app _).hom ∘ₗ LinearMap.proj j ∘ₗ LinearMap.proj i

def affineCechMap2 : AffineCech.Construction.affineCechC2 R F f →ₗ[R] AffineCech.Construction.affineCechC2 R G f :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    (φ.hom.app _).hom ∘ₗ LinearMap.proj k ∘ₗ LinearMap.proj j ∘ₗ LinearMap.proj i

theorem affineCechMap0_d (x : AffineCech.Construction.affineCechC0 R F f) :
    AffineCech.Construction.affineCechD0 R G f (affineCechMap0 R F f φ x) =
      affineCechMap1 R F f φ (AffineCech.Construction.affineCechD0 R F f x) := by
  funext i j
  simp [AffineCech.Construction.affineCechD0, affineCechMap0, affineCechMap1,
    AffineSectionCoordinates.Construction.affineBasicSectionRestriction_naturality R F φ]

theorem affineCechMap1_d (z : AffineCech.Construction.affineCechC1 R F f) :
    AffineCech.Construction.affineCechD1 R G f (affineCechMap1 R F f φ z) =
      affineCechMap2 R F f φ (AffineCech.Construction.affineCechD1 R F f z) := by
  funext i j k
  simp [AffineCech.Construction.affineCechD1, affineCechMap1, affineCechMap2,
    AffineSectionCoordinates.Construction.affineBasicSectionRestriction_naturality R F φ]

theorem affineCechMap2_injective
    (hφ : ∀ r : R, Function.Injective (φ.hom.app (op (PrimeSpectrum.basicOpen r)))) :
    Function.Injective (affineCechMap2 R F f φ) := by
  intro x y h
  funext i j k
  exact hφ _ (congrFun (congrFun (congrFun h i) j) k)

def affineCechUnit : F.obj.obj (op ⊤) →ₗ[R] AffineCech.Construction.affineCechC0 R F f :=
  LinearMap.pi fun i ↦ (F.obj.map (PrimeSpectrum.basicOpen (f i)).leTop.op).hom

theorem affineCechUnit_d (m : F.obj.obj (op ⊤)) :
    AffineCech.Construction.affineCechD0 R F f (affineCechUnit R F f m) = 0 := by
  apply (affineCechD0_eq_zero_iff R F f _).mpr
  intro i j
  change F.obj.map ((PrimeSpectrum.basicOpen (f i)).infLELeft (PrimeSpectrum.basicOpen (f j))).op
      (F.obj.map (PrimeSpectrum.basicOpen (f i)).leTop.op m) =
    F.obj.map ((PrimeSpectrum.basicOpen (f i)).infLERight (PrimeSpectrum.basicOpen (f j))).op
      (F.obj.map (PrimeSpectrum.basicOpen (f j)).leTop.op m)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← F.obj.map_comp, ← F.obj.map_comp]
  rfl

theorem affineCechUnit_naturality (m : F.obj.obj (op ⊤)) :
    affineCechMap0 R F f φ (affineCechUnit R F f m) =
      affineCechUnit R G f (φ.hom.app (op ⊤) m) := by
  funext i
  exact NatTrans.naturality_apply φ.hom (PrimeSpectrum.basicOpen (f i)).leTop.op m

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCechGluing.Construction
