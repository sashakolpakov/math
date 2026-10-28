import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledOrdinaryKernel
import OAI.AlgebraicGeometry.Picard.Homomorphisms.MultiplicativeSubgroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.AbelianSchemes

/-! # Unbundled Ordinary Fiber -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledOrdinaryFiber

noncomputable section

/-! Ordinarity is the equality of p-rank and the actual smooth dimension
on an algebraically closed fiber. No dimension is fixed on the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

def IsOrdinary (p : ℕ) {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] : Prop :=
  ∃ g : ℕ, SmoothOfRelativeDimension g A.hom ∧
    Nat.card (powMonoidHom p : (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker = p ^ g

namespace UnbundledPicard

variable (p : ℕ) [Fact p.Prime] {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)
variable (A : Over S) [GrpObj A] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian)
variable [IsMonHom ell] [IsFinite ell.left] [Surjective ell.left]
variable {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S)

include D ell in
theorem ordinary_geometricFiber_kernel_eq_multiplicativePTorsion
    (hordinary : IsOrdinary p (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A s)) :
    Subobject.mk ((Over.pullback s).map (Kernel.Construction.kernelInclusion
      (Frobenius.Construction.relativeFrobenius p Fact.out hS A))) =
        MultiplicativeSubgroup.Construction.multiplicativePTorsion p k (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A s) := by
  have : CharP k p := GeometricPoints.Construction.charP_of_geometric_map p Fact.out hS k s
  obtain ⟨g, hg, hcount⟩ := hordinary
  have : SmoothOfRelativeDimension g (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A s).hom := hg
  have : Smooth (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A s).hom := SmoothOfRelativeDimension.smooth g _
  have : IsProper (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A s).hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd A.hom s))
  have : GeometricallyConnected (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A s).hom :=
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd A.hom s))
  let ell' : UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A s ⟶ (D.pullback s).abelian := (Over.pullback s).map ell
  have : IsMonHom ell' := Functor.map.instIsMonHom (F := Over.pullback s) (f := ell) A D.abelian
  have : IsFinite ell'.left := MorphismProperty.overPullbackMap s ell (inferInstanceAs (IsFinite ell.left))
  have : Surjective ell'.left := MorphismProperty.overPullbackMap s ell (inferInstanceAs (Surjective ell.left))
  obtain ⟨i⟩ := UnbundledOrdinaryKernel.Construction.UnbundledPicard.ordinary_frobeniusKernel_multiplicative p (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A s) (D.pullback s)
    ell' g hcount
  have hi := MultiplicativeSubgroup.Construction.frobeniusKernel_eq_multiplicativePTorsion_of_iso p k (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A s) g i
  let e := FrobeniusKernelBaseChange.Construction.relativeFrobeniusKernelBaseChangeIso p Fact.out hS s A
  have he := FrobeniusKernelBaseChange.Construction.relativeFrobeniusKernelBaseChangeIso_inclusion p Fact.out hS s A
  have h := Subobject.mk_eq_mk_of_comm
    ((Over.pullback s).map (Kernel.Construction.kernelInclusion (Frobenius.Construction.relativeFrobenius p Fact.out hS A)))
    (Kernel.Construction.kernelInclusion (Frobenius.Construction.relativeFrobenius p Fact.out (Frobenius.Construction.prime_eq_zero_of_map p hS s)
      ((Over.pullback s).obj A))) e he
  exact h.trans hi

end UnbundledPicard

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledOrdinaryFiber
