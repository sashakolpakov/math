import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying
import OAI.ArithmeticGeometry.Descent.CMVariety.ModuliObjects
import Mathlib.CategoryTheory.Subfunctor.Image

/-! # Enhancement -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Enhancement

noncomputable section

/-! Record the integral PEL action by finitely many actual endomorphisms.
Preserving the chosen integral basis is equivalent to preserving the full action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

section IntegralAction

variable {O Idx : Type} [CommRing O] {S : Scheme} {g h : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B)
  (f : A.scheme ⟶ B.scheme) [IsMonHom f]

def postActionLinear : O →ₗ[ℤ] Additive (A.scheme ⟶ B.scheme) :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun a => Additive.ofMul (ρ.map a ≫ f)
    map_zero' := by rw [ρ.map_zero, MonObj.one_comp]; rfl
    map_add' := by intro a b; rw [ρ.map_add, MonObj.mul_comp]; rfl }

omit [IsMonHom f] in
def preActionLinear : O →ₗ[ℤ] Additive (A.scheme ⟶ B.scheme) :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun a => Additive.ofMul (f ≫ σ.map a)
    map_zero' := by rw [σ.map_zero, MonObj.comp_one]; rfl
    map_add' := by intro a b; rw [σ.map_add, MonObj.comp_mul]; rfl }

theorem action_equivariant_of_basis (b : Module.Basis Idx ℤ O)
    (hb : ∀ i, ρ.map (b i) ≫ f = f ≫ σ.map (b i)) :
    ∀ a : O, ρ.map a ≫ f = f ≫ σ.map a := by
  have he : postActionLinear A B ρ f = preActionLinear A B σ f :=
    b.ext (fun i => congrArg Additive.ofMul (hb i))
  intro a
  exact congrArg Additive.toMul (LinearMap.congr_fun he a)

end IntegralAction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {s N r : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T : Over (Spec (.of K))}

/-- Any finite integral basis records the entire PEL action in CMAbelianVariety's format. -/
def pelEnhancement (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T) :
    ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianData (3 * s) P.polarizationType N r T.left where
  polarized := A.polarized
  endomorphism i := A.action.map (b i)
  endomorphism_group i := A.action.preservesGroup (b i)

def pelEnhancementIso (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    {A B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T} (e : AbelianModuli.ReferenceFamily.PEL.Objects.PELIso A B) :
    ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianIso (pelEnhancement b A) (pelEnhancement b B) where
  polarized := e.polarized
  equivariant i := e.action (b i)

def pelIsoOfEnhancement (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    {A B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T}
    (e : ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianIso (pelEnhancement b A) (pelEnhancement b B)) :
    AbelianModuli.ReferenceFamily.PEL.Objects.PELIso A B := {
    polarized := e.polarized
    action := @action_equivariant_of_basis _ _ _ _ _ _
      A.polarized.abelian B.polarized.abelian A.action B.action
      e.polarized.abelian.hom e.polarized.abelianGroup b e.equivariant }

def pelEnhancementClasses (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E)) :
    AbelianModuli.ReferenceFamily.PEL.Objects.PELClasses P iota N T →
      ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianClasses (3 * s) P.polarizationType N r T.left :=
  Quotient.map (pelEnhancement b) (fun _ _ ⟨e⟩ => ⟨pelEnhancementIso b e⟩)

theorem pelEnhancementClasses_injective
    (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E)) :
    Function.Injective (pelEnhancementClasses (P := P) (iota := iota) (N := N) (T := T) b) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h A =>
    induction y using Quotient.inductionOn with
    | h B =>
      intro h
      obtain ⟨e⟩ := Quotient.exact h
      exact Quotient.sound ⟨pelIsoOfEnhancement b e⟩

theorem pelEnhancementClasses_pullback
    (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    {U : Over (Spec (.of K))} (f : T ⟶ U) (x : AbelianModuli.ReferenceFamily.PEL.Objects.PELClasses P iota N U) :
    pelEnhancementClasses b (AbelianModuli.ReferenceFamily.PEL.Objects.PELClasses.pullback f x) =
      ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianClasses.pullback f.left (pelEnhancementClasses b x) := by
  induction x using Quotient.inductionOn with
  | h A => rfl

def pelEnhancementTransformation
    (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E)) :
    AbelianModuli.ReferenceFamily.PEL.Classifying.pelModuliFunctor P iota N ⟶
      ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.enhancedAbelianModuliOver (3 * s) P.polarizationType N r (Spec (.of K)) where
  app T := TypeCat.ofHom (pelEnhancementClasses b)
  naturality T U f := by
    ext x
    exact pelEnhancementClasses_pullback b f.unop x

/-- The PEL locus is an actual subfunctor of CMAbelianVariety's enhanced moduli functor. -/
def pelEnhancementLocus
    (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E)) :
    Subfunctor (ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.enhancedAbelianModuliOver (3 * s) P.polarizationType N r (Spec (.of K))) :=
  Subfunctor.range (pelEnhancementTransformation (P := P) (iota := iota) b)

theorem pelClassifying_bijective
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
    (T : Over (Spec (.of K))) :
    Function.Bijective (fun f : T ⟶ M.space => (M.universal.pullback f).classOf) := by
  constructor
  · intro f g hfg
    have hf : Nonempty (AbelianModuli.ReferenceFamily.Models.PELPullbackIso M.universal (M.universal.pullback f) f) :=
      (AbelianModuli.ReferenceFamily.Models.PELPullbackIso.nonempty_iff_classOf f).mpr rfl
    have hg : Nonempty (AbelianModuli.ReferenceFamily.Models.PELPullbackIso M.universal (M.universal.pullback f) g) :=
      (AbelianModuli.ReferenceFamily.Models.PELPullbackIso.nonempty_iff_classOf g).mpr hfg
    exact ExistsUnique.unique (hM T (M.universal.pullback f)) hf hg
  · intro x
    obtain ⟨A, rfl⟩ := Quotient.exists_rep x
    obtain ⟨f, hf, _⟩ := hM T A
    exact ⟨f, ((AbelianModuli.ReferenceFamily.Models.PELPullbackIso.nonempty_iff_classOf f).mp hf).symm⟩

/-- The explicit IsFine predicate provides representability on all test schemes. -/
def pelRepresentable (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) :
    (AbelianModuli.ReferenceFamily.PEL.Classifying.pelModuliFunctor P iota N).RepresentableBy M.space where
  homEquiv := Equiv.ofBijective _ (pelClassifying_bijective M hM _)
  homEquiv_comp f g := AbelianModuli.ReferenceFamily.PEL.Objects.PELClasses.pullback_comp g f M.universal.classOf

/-- The same actual PEL moduli space represents its locus in the finite
enhanced moduli problem, as required by CMAbelianVariety. -/
def pelEnhancementRepresentable
    (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) :
    (pelEnhancementLocus (P := P) (iota := iota) (N := N) b).toFunctor.RepresentableBy M.space := by
  let α := pelEnhancementTransformation (P := P) (iota := iota) (N := N) b
  let β := Subfunctor.toRange α
  let hβ : IsIso β := (NatTrans.isIso_iff_isIso_app β).mpr (fun T =>
    (CategoryTheory.isIso_iff_bijective (β.app T)).mpr (by
      constructor
      · intro x y h
        apply pelEnhancementClasses_injective b
        exact congrArg Subtype.val h
      · rintro ⟨y, x, hx⟩
        exact ⟨x, Subtype.ext hx⟩))
  exact (pelRepresentable M hM).ofIso (@asIso _ _ _ _ β hβ)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Enhancement
