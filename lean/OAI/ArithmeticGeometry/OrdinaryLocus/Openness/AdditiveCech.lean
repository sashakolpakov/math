import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineExtOne
import Mathlib.Algebra.Category.Grp.Biproducts

/-! # Additive Cech -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveCech.Construction

noncomputable section

/-! Additive Čech cochains for arbitrary abelian sheaves on an affine spectrum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v

variable (R : CommRingCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (PrimeSpectrum R)))
    {ι : Type v} (f : ι → R)

abbrev additiveAffineC0 := ∀ i, F.obj.obj (op (PrimeSpectrum.basicOpen (f i)))
abbrev additiveAffineC1 := ∀ i j, F.obj.obj (op (PrimeSpectrum.basicOpen (f i * f j)))
abbrev additiveAffineC2 := ∀ i j k, F.obj.obj (op (PrimeSpectrum.basicOpen (f i * (f j * f k))))

@[simps]
def additiveC1Eval (i j : ι) : additiveAffineC1 R F f →+
    F.obj.obj (op (PrimeSpectrum.basicOpen (f i * f j))) where
  toFun z := z i j
  map_zero' := rfl
  map_add' _ _ := rfl

@[simps]
def additiveC2Eval (i j k : ι) : additiveAffineC2 R F f →+
    F.obj.obj (op (PrimeSpectrum.basicOpen (f i * (f j * f k)))) where
  toFun z := z i j k
  map_zero' := rfl
  map_add' _ _ := rfl

def additiveBasicRestriction (r h : R) (hrh : r ∣ h) :
    F.obj.obj (op (PrimeSpectrum.basicOpen r)) →+ F.obj.obj (op (PrimeSpectrum.basicOpen h)) :=
  (F.obj.map (homOfLE (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R r h hrh)).op).hom

theorem additiveBasicRestriction_comp_apply (r g h : R) (hrg : r ∣ g) (hgh : g ∣ h)
    (x : F.obj.obj (op (PrimeSpectrum.basicOpen r))) :
    additiveBasicRestriction R F g h hgh (additiveBasicRestriction R F r g hrg x) =
      additiveBasicRestriction R F r h (hrg.trans hgh) x := by
  change (F.obj.map (homOfLE (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R g h hgh)).op)
    (F.obj.map (homOfLE (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R r g hrg)).op x) = _
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  rfl

theorem additiveBasicRestriction_naturality
    {G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (PrimeSpectrum R))}
    (φ : F ⟶ G) (r h : R) (hrh : r ∣ h) (x : F.obj.obj (op (PrimeSpectrum.basicOpen r))) :
    additiveBasicRestriction R G r h hrh (φ.hom.app _ x) =
      φ.hom.app _ (additiveBasicRestriction R F r h hrh x) :=
  (NatTrans.naturality_apply φ.hom
    (homOfLE (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R r h hrh)).op x).symm

def additiveAffineD0 : additiveAffineC0 R F f →+ additiveAffineC1 R F f :=
  AddMonoidHom.pi fun i ↦ AddMonoidHom.pi fun j ↦
    (additiveBasicRestriction R F (f j) (f i * f j) (dvd_mul_left _ _)).comp (Pi.evalAddMonoidHom _ j) -
      (additiveBasicRestriction R F (f i) (f i * f j) (dvd_mul_right _ _)).comp (Pi.evalAddMonoidHom _ i)

def additiveAffineD1 : additiveAffineC1 R F f →+ additiveAffineC2 R F f :=
  AddMonoidHom.pi fun i ↦ AddMonoidHom.pi fun j ↦ AddMonoidHom.pi fun k ↦
    (additiveBasicRestriction R F (f j * f k) (f i * (f j * f k)) (dvd_mul_left _ _)).comp
      (additiveC1Eval R F f j k) -
    (additiveBasicRestriction R F (f i * f k) (f i * (f j * f k)) (by use f j; ring)).comp
      (additiveC1Eval R F f i k) +
    (additiveBasicRestriction R F (f i * f j) (f i * (f j * f k)) (by use f k; ring)).comp
      (additiveC1Eval R F f i j)

theorem additivePair_restriction_eq_iff
    {U V W : TopologicalSpace.Opens (PrimeSpectrum R)} (hW : W = U ⊓ V)
    (hU : W ≤ U) (hV : W ≤ V) (x : F.obj.obj (op U)) (y : F.obj.obj (op V)) :
    F.obj.map (homOfLE hU).op x = F.obj.map (homOfLE hV).op y ↔
      F.obj.map (U.infLELeft V).op x = F.obj.map (U.infLERight V).op y := by
  subst W
  rfl

theorem additiveAffineD0_eq_zero_iff (x : additiveAffineC0 R F f) :
    additiveAffineD0 R F f x = 0 ↔
      TopCat.Presheaf.IsCompatible F.obj (fun i ↦ PrimeSpectrum.basicOpen (f i)) x := by
  constructor
  · intro hx i j
    have h := congrFun (congrFun hx i) j
    change additiveBasicRestriction R F (f j) (f i * f j) (dvd_mul_left _ _) (x j) -
      additiveBasicRestriction R F (f i) (f i * f j) (dvd_mul_right _ _) (x i) = 0 at h
    have h' := (sub_eq_zero.mp h).symm
    exact (additivePair_restriction_eq_iff R F (PrimeSpectrum.basicOpen_mul _ _)
      (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R _ _ (dvd_mul_right _ _))
      (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R _ _ (dvd_mul_left _ _)) (x i) (x j)).mp h'
  · intro hx
    funext i j
    change additiveBasicRestriction R F (f j) (f i * f j) (dvd_mul_left _ _) (x j) -
      additiveBasicRestriction R F (f i) (f i * f j) (dvd_mul_right _ _) (x i) = 0
    apply sub_eq_zero.mpr
    exact ((additivePair_restriction_eq_iff R F (PrimeSpectrum.basicOpen_mul _ _)
      (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R _ _ (dvd_mul_right _ _))
      (AffineSectionCoordinates.Construction.principalBasicOpen_le_of_dvd R _ _ (dvd_mul_left _ _)) (x i) (x j)).mpr (hx i j)).symm

theorem additiveAffine_sections_glue (hf : Ideal.span (Set.range f) = ⊤)
    (x : additiveAffineC0 R F f) (hx : additiveAffineD0 R F f x = 0) :
    ∃! m : F.obj.obj (op ⊤), ∀ i, F.obj.map (PrimeSpectrum.basicOpen (f i)).leTop.op m = x i := by
  exact F.existsUnique_gluing' (fun i ↦ PrimeSpectrum.basicOpen (f i)) ⊤
    (fun _ ↦ homOfLE le_top)
    (by rw [(PrimeSpectrum.iSup_basicOpen_eq_top_iff).mpr hf]) x
    ((additiveAffineD0_eq_zero_iff R F f x).mp hx)

theorem additiveAffineD1_comp_D0 : (additiveAffineD1 R F f).comp (additiveAffineD0 R F f) = 0 := by
  apply AddMonoidHom.ext
  intro x
  funext i j k
  simp [additiveC1Eval, additiveAffineD0, additiveAffineD1, additiveBasicRestriction_comp_apply R F]

variable {G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (PrimeSpectrum R))} (φ : F ⟶ G)

def additiveAffineMap0 : additiveAffineC0 R F f →+ additiveAffineC0 R G f :=
  AddMonoidHom.pi fun i ↦ (φ.hom.app _).hom.comp (Pi.evalAddMonoidHom _ i)

def additiveAffineMap1 : additiveAffineC1 R F f →+ additiveAffineC1 R G f :=
  AddMonoidHom.pi fun i ↦ AddMonoidHom.pi fun j ↦
    (φ.hom.app _).hom.comp (additiveC1Eval R F f i j)

def additiveAffineMap2 : additiveAffineC2 R F f →+ additiveAffineC2 R G f :=
  AddMonoidHom.pi fun i ↦ AddMonoidHom.pi fun j ↦ AddMonoidHom.pi fun k ↦
    (φ.hom.app _).hom.comp (additiveC2Eval R F f i j k)

theorem additiveAffineMap0_d (x : additiveAffineC0 R F f) :
    additiveAffineD0 R G f (additiveAffineMap0 R F f φ x) =
      additiveAffineMap1 R F f φ (additiveAffineD0 R F f x) := by
  funext i j
  simp [additiveC1Eval, additiveAffineD0, additiveAffineMap0, additiveAffineMap1,
    additiveBasicRestriction_naturality R F φ]

theorem additiveAffineMap1_d (z : additiveAffineC1 R F f) :
    additiveAffineD1 R G f (additiveAffineMap1 R F f φ z) =
      additiveAffineMap2 R F f φ (additiveAffineD1 R F f z) := by
  funext i j k
  simp [additiveC1Eval, additiveC2Eval, additiveAffineD1, additiveAffineMap1, additiveAffineMap2,
    additiveBasicRestriction_naturality R F φ]

theorem additiveAffineMap2_injective
    (hφ : ∀ r : R, Function.Injective (φ.hom.app (op (PrimeSpectrum.basicOpen r)))) :
    Function.Injective (additiveAffineMap2 R F f φ) := by
  intro x y h
  funext i j k
  exact hφ _ (congrFun (congrFun (congrFun h i) j) k)

def additiveAffineUnit : F.obj.obj (op ⊤) →+ additiveAffineC0 R F f :=
  AddMonoidHom.pi fun i ↦ (F.obj.map (PrimeSpectrum.basicOpen (f i)).leTop.op).hom

theorem additiveAffineUnit_d (m : F.obj.obj (op ⊤)) :
    additiveAffineD0 R F f (additiveAffineUnit R F f m) = 0 := by
  apply (additiveAffineD0_eq_zero_iff R F f _).mpr
  intro i j
  change F.obj.map ((PrimeSpectrum.basicOpen (f i)).infLELeft (PrimeSpectrum.basicOpen (f j))).op
      (F.obj.map (PrimeSpectrum.basicOpen (f i)).leTop.op m) =
    F.obj.map ((PrimeSpectrum.basicOpen (f i)).infLERight (PrimeSpectrum.basicOpen (f j))).op
      (F.obj.map (PrimeSpectrum.basicOpen (f j)).leTop.op m)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← F.obj.map_comp]
  rfl

theorem additiveAffineUnit_naturality (m : F.obj.obj (op ⊤)) :
    additiveAffineMap0 R F f φ (additiveAffineUnit R F f m) =
      additiveAffineUnit R G f (φ.hom.app (op ⊤) m) := by
  funext i
  exact NatTrans.naturality_apply φ.hom (PrimeSpectrum.basicOpen (f i)).leTop.op m

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveCech.Construction
