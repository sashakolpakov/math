import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OrthogonalProjectors
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum

/-! # Decomposition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Decomposition.Construction

noncomputable section

/-!
Complete orthogonal scheme projectors give a natural product decomposition
on every test scheme. Applied to CMPoints's integral lifts, this is the actual
full torsion decomposition into the native IsogenyQuotient blocks.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u v

section Native

variable {S : Scheme.{u}} {T : Over S} [GrpObj T] [IsCommMonObj T]

def precompositionPointHom {X : Over S} (x : X ⟶ T) : (T ⟶ T) →* (X ⟶ T) where
  toFun f := x ≫ f
  map_one' := MonObj.comp_one x
  map_mul' f g := MonObj.comp_mul x f g

def fixedPointPointsMulEquiv (p : T ⟶ T) [IsMonHom p] (X : Over S) :
    (X ⟶ BlockGroups.Construction.fixedPointScheme p) ≃*
      (IsMonHom.monoidHom p X).eqLocus (MonoidHom.id (X ⟶ T)) where
  toFun f := ⟨f ≫ BlockGroups.Construction.fixedPointInclusion p, by
    change (f ≫ BlockGroups.Construction.fixedPointInclusion p) ≫ p = f ≫ BlockGroups.Construction.fixedPointInclusion p
    rw [Category.assoc, BlockGroups.Construction.fixedPointInclusion_fixed]⟩
  invFun x := BlockGroups.Construction.fixedPointLift p x.val x.property
  left_inv f := by
    apply (cancel_mono (BlockGroups.Construction.fixedPointInclusion p)).mp
    exact BlockGroups.Construction.fixedPointLift_inclusion _ _ _
  right_inv x := Subtype.ext (BlockGroups.Construction.fixedPointLift_inclusion _ _ _)
  map_mul' f g := Subtype.ext (MonObj.mul_comp f g _)

theorem fixedPointPointsMulEquiv_symm_inclusion (p : T ⟶ T) [IsMonHom p] (X : Over S)
    (x : (IsMonHom.monoidHom p X).eqLocus (MonoidHom.id (X ⟶ T))) :
    (fixedPointPointsMulEquiv p X).symm x ≫ BlockGroups.Construction.fixedPointInclusion p = x.val :=
  BlockGroups.Construction.fixedPointLift_inclusion p x.val x.property

variable {I : Type v} [Fintype I]
  (p : I → (T ⟶ T)) [∀ i, IsMonHom (p i)]
  (horth : ∀ i j, i ≠ j → p i ≫ p j = 1)
  (hcomplete : (∏ i, p i) = 𝟙 T)

def schemeProjectorPointEquiv (X : Over S) :
    (X ⟶ T) ≃* (∀ i, X ⟶ BlockGroups.Construction.fixedPointScheme (p i)) :=
  (OrthogonalProjectors.Construction.orthogonalProjectorEquiv (fun i => IsMonHom.monoidHom (p i) X)
    (by
      intro i j hij x
      change (x ≫ p j) ≫ p i = 1
      rw [Category.assoc, horth j i hij.symm, MonObj.comp_one])
    (by
      intro x
      change (∏ i, precompositionPointHom x (p i)) = x
      rw [← map_prod, hcomplete]
      exact Category.comp_id x)).trans
      (MulEquiv.piCongrRight (fun i => (fixedPointPointsMulEquiv (p i) X).symm))

theorem schemeProjectorPointEquiv_inclusion (X : Over S) (x : X ⟶ T) (i : I) :
    schemeProjectorPointEquiv p horth hcomplete X x i ≫ BlockGroups.Construction.fixedPointInclusion (p i) = x ≫ p i := by
  simp only [schemeProjectorPointEquiv, MulEquiv.trans_apply, MulEquiv.piCongrRight_apply,
    fixedPointPointsMulEquiv_symm_inclusion]
  rfl

theorem schemeProjectorPointEquiv_naturality {X Y : Over S} (f : X ⟶ Y) (x : Y ⟶ T) (i : I) :
    schemeProjectorPointEquiv p horth hcomplete X (f ≫ x) i =
      f ≫ schemeProjectorPointEquiv p horth hcomplete Y x i := by
  apply (cancel_mono (BlockGroups.Construction.fixedPointInclusion (p i))).mp
  calc
    _ = (f ≫ x) ≫ p i := schemeProjectorPointEquiv_inclusion p horth hcomplete X (f ≫ x) i
    _ = f ≫ (x ≫ p i) := Category.assoc f x (p i)
    _ = f ≫ (schemeProjectorPointEquiv p horth hcomplete Y x i ≫ BlockGroups.Construction.fixedPointInclusion (p i)) :=
      congrArg (fun z => f ≫ z) (schemeProjectorPointEquiv_inclusion p horth hcomplete Y x i).symm
    _ = _ := (Category.assoc _ _ _).symm

end Native

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

/-- Actual torsion points decompose into all native split blocks, on
arbitrary test schemes, including nonreduced schemes. -/
def l45TorsionPointDecomposition (n : ℕ) (X : Over S) :
    (X ⟶ Groups.Construction.nativeTorsionScheme A.scheme (q ^ n)) ≃*
      (∀ τ : Gal(E/ℚ), X ⟶ OppositeKernel.Construction.torsionBlock (q ^ n) (σ.map (j.projector iota hsplit n τ))) :=
  schemeProjectorPointEquiv
    (fun τ => Groups.Construction.nativeTorsionMap (q ^ n) (σ.map (j.projector iota hsplit n τ)))
    (CM.PointsProjectorSum.Construction.l45_native_projectors_orthogonal j iota hsplit A σ n)
    (CM.PointsProjectorSum.Construction.l45_native_projectors_complete j iota hsplit A σ n) X

theorem l45TorsionPointDecomposition_naturality (n : ℕ)
    {X Y : Over S} (f : X ⟶ Y) (x : Y ⟶ Groups.Construction.nativeTorsionScheme A.scheme (q ^ n)) (τ : Gal(E/ℚ)) :
    l45TorsionPointDecomposition j iota hsplit A σ n X (f ≫ x) τ =
      f ≫ l45TorsionPointDecomposition j iota hsplit A σ n Y x τ :=
  schemeProjectorPointEquiv_naturality _ _ _ f x τ

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Decomposition.Construction
