import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Immersion Kernel Iso -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionKernelIso

noncomputable section

/-! Closed immersions with the same actual ideal sheaf determine a unique
embedding-compatible isomorphism of their source schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X)
variable [IsClosedImmersion f] [IsClosedImmersion g] (h : f.ker = g.ker)

def closedImmersionKernelIso : A ≅ B := by
  let k := IsClosedImmersion.lift g f h.ge
  have : IsIso k := IsClosedImmersion.isIso_lift g f h.symm
  exact asIso k

@[reassoc]
theorem closedImmersionKernelIso_hom : (closedImmersionKernelIso f g h).hom ≫ g = f :=
  IsClosedImmersion.lift_fac g f h.ge

@[reassoc]
theorem closedImmersionKernelIso_inv : (closedImmersionKernelIso f g h).inv ≫ f = g := by
  exact (congrArg (fun k => (closedImmersionKernelIso f g h).inv ≫ k)
    (closedImmersionKernelIso_hom f g h)).symm.trans (Iso.inv_hom_id_assoc _ _)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionKernelIso
