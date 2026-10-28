import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Cech

/-! # Supported -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison

noncomputable section

/-! The actual local PD-to-injective map followed by supported Čech
descent and excision gives a class in the original bounded cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex w n I

def opens : C ⥤ Y.left.Opens :=
  AffinePrincipal.Diagram.functor X.left U.val U.property ⋙
    SectionBifunctor.specialOpens p k n X Y f

def source := Principal.Comparison.source p k n X Y f hp U

def coefficientMap : source p k n X Y f hp U ⟶
    Supported.OrderedCechEdge.presheafComplex.{1,0,0,2}
      R Y.left.carrier (opens p k n X Y f U) K :=
  Principal.Comparison.map p k n X Y f hp U I

def family (g : ℕ) (a : Fin g → Γ(X.left, U.val)) : ULift (Fin g) → C :=
  fun i => ⟨a i.down⟩

def toBounded (g : ℕ) (a : Fin g → Γ(X.left, U.val)) (O : Y.left.Opens)
    (hO : ∀ i, (opens p k n X Y f U).obj (family p k n X U g a i) ≤ O)
    (hcover : (opens p k n X Y f U).obj (⊤_ C) ⊓ O ≤
      ⨆ i, (opens p k n X Y f U).obj (family p k n X U g a i))
    (hrows : ∀ q r, ((BoundedSupported.Cech.bicomplex w n I
      (opens p k n X Y f U) (family p k n X U g a)).X q).ExactAt (r + 1))
    (hglobal : (opens p k n X Y f U).obj (⊤_ C) ⊔ O = ⊤) (i : ℕ) :=
  BoundedSupported.Cech.map w n I (opens p k n X Y f U) (family p k n X U g a)
    O hO hcover hrows hglobal (source p k n X Y f hp U) (coefficientMap p k n X Y f hp U I) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison
