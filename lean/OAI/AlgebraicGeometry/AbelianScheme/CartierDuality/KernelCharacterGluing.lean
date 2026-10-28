import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfScalarsOf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ScalarLineGluing
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterDetection

/-! # Kernel Character Gluing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterGluing

noncomputable section

/-!
# CartierDuality: actual kernel characters construct the line-descent cocycle
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterDetection.Construction
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- The unique kernel element carrying one equal-image point to another. -/
def kernelDifference {T : Over S} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f :=
  Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift f (x⁻¹ * y) (by rw [MonObj.mul_comp, GrpObj.inv_comp, h, inv_mul_cancel])

theorem kernelDifference_inclusion {T : Over S} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    kernelDifference f x y h ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f = x⁻¹ * y := Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift_inclusion _ _ _

theorem kernelDifference_self {T : Over S} (x : T ⟶ A) : kernelDifference f x x rfl = 1 := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [kernelDifference_inclusion, MonObj.one_comp, inv_mul_cancel]

theorem kernelDifference_congr {T : Over S} (x y x' y' : T ⟶ A)
    (h : x ≫ f = y ≫ f) (h' : x' ≫ f = y' ≫ f) (hx : x = x') (hy : y = y') :
    kernelDifference f x y h = kernelDifference f x' y' h' := by
  subst x'
  subst y'
  rfl

theorem kernelDifference_comp {T : Over S} (x y z : T ⟶ A)
    (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) :
    kernelDifference f x y hxy * kernelDifference f y z hyz =
      kernelDifference f x z (hxy.trans hyz) := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [MonObj.mul_comp, kernelDifference_inclusion, kernelDifference_inclusion, kernelDifference_inclusion]
  group

theorem kernelDifference_natural {T U : Over S} (t : U ⟶ T) (x y : T ⟶ A)
    (h : x ≫ f = y ≫ f) :
    t ≫ kernelDifference f x y h = kernelDifference f (t ≫ x) (t ≫ y)
      (by rw [Category.assoc, h, Category.assoc]) := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [Category.assoc, kernelDifference_inclusion, kernelDifference_inclusion,
    MonObj.comp_mul, GrpObj.comp_inv]

/-- A native test-scheme map into the cover, over the induced base map. -/
def coverPoint {T : Scheme.{u}} (q : T ⟶ B.left) (x : T ⟶ A.left) (hx : x ≫ f.left = q) :
    Over.mk (q ≫ B.hom) ⟶ A := Over.homMk x (by rw [← f.w, ← Category.assoc, hx]; rfl)

omit [GrpObj A] [GrpObj B] [IsMonHom f] in
theorem coverPoint_comp {T : Scheme.{u}} (q : T ⟶ B.left) (x : T ⟶ A.left) (hx : x ≫ f.left = q) :
    coverPoint f q x hx ≫ f = (Over.homMk q rfl : Over.mk (q ≫ B.hom) ⟶ B) :=
  Over.OverMorphism.ext hx

variable (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)

/-- Evaluate the actual character on the canonical difference element. -/
def differenceScalar {T : Scheme.{u}} (q : T ⟶ B.left) (x y : T ⟶ A.left)
    (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) : Γ(T, ⊤) :=
  (χ (Over.mk (q ≫ B.hom)) (kernelDifference f (coverPoint f q x hx) (coverPoint f q y hy)
    ((coverPoint_comp f q x hx).trans (coverPoint_comp f q y hy).symm))).val

theorem differenceScalar_self {T : Scheme.{u}} (q : T ⟶ B.left) (x : T ⟶ A.left)
    (hx : x ≫ f.left = q) : differenceScalar f χ q x x hx hx = 1 := by
  unfold differenceScalar
  rw [kernelDifference_self, map_one]
  rfl

theorem differenceScalar_comp {T : Scheme.{u}} (q : T ⟶ B.left) (x y z : T ⟶ A.left)
    (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) (hz : z ≫ f.left = q) :
    differenceScalar f χ q x y hx hy * differenceScalar f χ q y z hy hz =
      differenceScalar f χ q x z hx hz := by
  unfold differenceScalar
  rw [← Units.val_mul, ← map_mul, kernelDifference_comp]

variable (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
  Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

include hχ in
theorem differenceScalar_natural {T U : Scheme.{u}} (t : U ⟶ T) (q : T ⟶ B.left)
    (x y : T ⟶ A.left) (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) :
    t.appTop (differenceScalar f χ q x y hx hy) =
      differenceScalar f χ (t ≫ q) (t ≫ x) (t ≫ y)
        (by rw [Category.assoc, hx]) (by rw [Category.assoc, hy]) := by
  let a : Over.mk ((t ≫ q) ≫ B.hom) ⟶ Over.mk (q ≫ B.hom) := Over.homMk t (Category.assoc t q B.hom)
  let px := coverPoint f q x hx
  let py := coverPoint f q y hy
  let d := kernelDifference f px py ((coverPoint_comp f q x hx).trans (coverPoint_comp f q y hy).symm)
  have hn := congrArg Units.val (hχ a d)
  have hd := kernelDifference_natural f a px py
    ((coverPoint_comp f q x hx).trans (coverPoint_comp f q y hy).symm)
  have hx' : a ≫ px = coverPoint f (t ≫ q) (t ≫ x) (by rw [Category.assoc, hx]) :=
    Over.OverMorphism.ext rfl
  have hy' : a ≫ py = coverPoint f (t ≫ q) (t ≫ y) (by rw [Category.assoc, hy]) :=
    Over.OverMorphism.ext rfl
  have hd' := hd.trans (kernelDifference_congr f (a ≫ px) (a ≫ py)
    (coverPoint f (t ≫ q) (t ≫ x) (by rw [Category.assoc, hx]))
    (coverPoint f (t ≫ q) (t ≫ y) (by rw [Category.assoc, hy])) _
    ((coverPoint_comp f (t ≫ q) (t ≫ x) (by rw [Category.assoc, hx])).trans
      (coverPoint_comp f (t ≫ q) (t ≫ y) (by rw [Category.assoc, hy])).symm) hx' hy')
  exact hn.trans (congrArg (fun z => (χ (Over.mk ((t ≫ q) ≫ B.hom)) z).val) hd')

/-- An actual natural kernel character gives a scalar Cech cocycle
for the native scheme morphism over any base. -/
def characterScalarCocycle : ScalarLineGluing.Construction.LineDescent.ScalarCocycle f.left where
  value := differenceScalar f χ
  self := differenceScalar_self f χ
  comp := differenceScalar_comp f χ
  naturality := differenceScalar_natural f χ hχ

/-- The character acts on the trivial line to give actual native
line-bundle descent data. -/
def characterLineDatum : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f.left := (characterScalarCocycle f χ hχ).nativeDatum

/-- The native gluing has precisely the original character's value on
the difference of the two covering points. -/
theorem characterLineDatum_scalar {T : Scheme.{u}} (q : T ⟶ B.left) (x y : T ⟶ A.left)
    (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (characterLineDatum f χ hχ) (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left))
      q x y hx hy = differenceScalar f χ q x y hx hy :=
  ScalarLineGluing.Construction.LineDescent.ScalarCocycle.nativeDatum_scalar (characterScalarCocycle f χ hχ) q x y hx hy

/-- Actual Hopf-coordinate characters supply the natural unit-valued
character on an affine presented native kernel. -/
def hopfKernelUnitHom {R C : Type u} [CommRing R] [CommRing C] [HopfAlgebra R C]
    {A B : Over (Spec (.of R))} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (i : Characters.Construction.affineHopfGroupScheme R C ≅ Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) (z : GroupLike R C)
    (T : Over (Spec (.of R))) : (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ :=
  (HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom R C z T).comp (IsMonHom.monoidHom i.inv.hom.hom T)

theorem hopfKernelUnitHom_natural {R C : Type u} [CommRing R] [CommRing C] [HopfAlgebra R C]
    {A B : Over (Spec (.of R))} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (i : Characters.Construction.affineHopfGroupScheme R C ≅ Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) (z : GroupLike R C)
    {T U : Over (Spec (.of R))} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    Units.map t.left.appTop.hom (hopfKernelUnitHom f i z T x) = hopfKernelUnitHom f i z U (t ≫ x) :=
  (HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom_natural R C z t (x ≫ i.inv.hom.hom)).trans
    (congrArg (HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom R C z U) (Category.assoc t x i.inv.hom.hom).symm)

/-- An actual Hopf character of a native kernel constructs ordinary
native line descent over every commutative base ring. -/
def hopfCharacterLineDatum {R C : Type u} [CommRing R] [CommRing C] [HopfAlgebra R C]
    {A B : Over (Spec (.of R))} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (i : Characters.Construction.affineHopfGroupScheme R C ≅ Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) (z : GroupLike R C) :
    Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f.left :=
  characterLineDatum f (hopfKernelUnitHom f i z) (hopfKernelUnitHom_natural f i z)

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterGluing
