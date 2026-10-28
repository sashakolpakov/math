import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteTorsion
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Action
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteOverField
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Assembly
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Torsion.Construction

noncomputable section

/-!
The actual relative Frobenius kernel is killed by p. Naturality first
shows that its own Frobenius vanishes; the finite Hopf height-one argument
then embeds the entire kernel scheme into A[p], retaining infinitesimals.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

abbrev geometricFrobeniusIsogeny := Action.Construction.frobeniusIsogeny p (Fact.out : p.Prime)
  (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A

abbrev nativeFrobeniusKernel : Grp (Over (Spec (.of k))) :=
  @Grp.mk _ _ _ (Picard.PoincareBundle.Kernel.Scheme.kernelObject (geometricFrobeniusIsogeny p k A).hom)
    (Picard.PoincareBundle.Kernel.Scheme.kernelGroup (geometricFrobeniusIsogeny p k A).hom)

instance nativeFrobeniusKernel_finite : IsFinite (nativeFrobeniusKernel p k A).X.hom :=
  Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite (geometricFrobeniusIsogeny p k A).hom

instance nativeFrobeniusKernel_commutative : IsCommMonObj (nativeFrobeniusKernel p k A).X :=
  Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative (geometricFrobeniusIsogeny p k A).hom

omit [IsAlgClosed k] in
theorem nativeFrobeniusKernel_frobenius :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))
        (nativeFrobeniusKernel p k A).X = 1 := by
  let hp : p.Prime := Fact.out
  let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := (geometricFrobeniusIsogeny p k A).hom
  let H := (nativeFrobeniusKernel p k A).X
  let i : H ⟶ A.scheme := Picard.PoincareBundle.Kernel.Scheme.kernelInclusion F
  have : Mono i := inferInstanceAs (Mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion F))
  have : IsMonHom i := inferInstanceAs (IsMonHom (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion F))
  let P := Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp _ hS)
  let j : Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS H ⟶ Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS A.scheme := P.map i
  have : Mono j := inferInstanceAs (Mono (P.map i))
  have : IsMonHom j := Functor.map.instIsMonHom (F := P) (f := i) H A.scheme
  apply (cancel_mono j).mp
  have hn := (Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat p hp hS).naturality i
  have hi : i ≫ F = 1 := Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp F
  exact hn.symm.trans (hi.trans (MonObj.one_comp j).symm)

/-- Multiplication by p vanishes on the whole relative Frobenius kernel. -/
theorem nativeFrobeniusKernel_killed : (𝟙 (nativeFrobeniusKernel p k A).X) ^ p = 1 := by
  have hflat := FiniteOverField.Construction.finiteOverField_finiteLocallyFree (nativeFrobeniusKernel p k A).X.hom
  have : Flat (nativeFrobeniusKernel p k A).X.hom := hflat.1
  have : LocallyOfFinitePresentation (nativeFrobeniusKernel p k A).X.hom := hflat.2
  exact FiniteTorsion.Construction.finiteGroup_killed_of_trivial_frobenius p k (nativeFrobeniusKernel p k A)
    (nativeFrobeniusKernel_frobenius p k A)

theorem nativeFrobeniusKernelInclusion_killed :
    (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (geometricFrobeniusIsogeny p k A).hom) ^ p = 1 := by
  let i := Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (geometricFrobeniusIsogeny p k A).hom
  have hi : IsMonHom i := inferInstance
  have h := congrArg (fun f => f ≫ i) (nativeFrobeniusKernel_killed p k A)
  rw [MonObj.pow_comp, Category.id_comp, MonObj.one_comp] at h
  exact h

/-- The canonical map embeds the native Frobenius kernel in scheme-theoretic
p-torsion by the zero-fiber universal property. -/
def nativeFrobeniusKernelToTorsion : (nativeFrobeniusKernel p k A).X ⟶ A.torsionScheme p :=
  (A.torsionSchemePointsEquiv p (nativeFrobeniusKernel p k A).X).symm
    ⟨Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (geometricFrobeniusIsogeny p k A).hom,
      nativeFrobeniusKernelInclusion_killed p k A⟩

theorem nativeFrobeniusKernelToTorsion_inclusion :
    nativeFrobeniusKernelToTorsion p k A ≫ A.torsionInclusion p =
      Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (geometricFrobeniusIsogeny p k A).hom :=
  congrArg (fun x : A.torsionPoints p (nativeFrobeniusKernel p k A).X => x.val)
    ((A.torsionSchemePointsEquiv p (nativeFrobeniusKernel p k A).X).apply_symm_apply _)

instance nativeFrobeniusKernelToTorsion_isMonHom :
    IsMonHom (nativeFrobeniusKernelToTorsion p k A) := by
  apply RepresentedGroups.Construction.isMonHom_of_point_operations
  · intro T
    apply (cancel_mono (A.torsionInclusion p)).mp
    rw [Category.assoc, nativeFrobeniusKernelToTorsion_inclusion,
      MonObj.one_comp, MonObj.one_comp]
  · intro T x y
    apply (cancel_mono (A.torsionInclusion p)).mp
    rw [Category.assoc, nativeFrobeniusKernelToTorsion_inclusion, MonObj.mul_comp,
      MonObj.mul_comp, Category.assoc, Category.assoc, nativeFrobeniusKernelToTorsion_inclusion]

instance nativeFrobeniusKernelToTorsion_mono : Mono (nativeFrobeniusKernelToTorsion p k A) :=
  mono_of_mono_fac (nativeFrobeniusKernelToTorsion_inclusion p k A)

theorem nativeFrobeniusKernelToTorsion_closed :
    IsClosedImmersion (nativeFrobeniusKernelToTorsion p k A).left :=
  OrdinaryBlocks.Construction.closedSubgroupOfFiniteMono (nativeFrobeniusKernelToTorsion p k A)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Torsion.Construction
