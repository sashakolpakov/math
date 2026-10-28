import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Assembly

/-! # Assembly Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AssemblyTransport.Construction

noncomputable section

/-! Changing an equal torsion index preserves the actual full-kernel map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem fullKernelToAbelian_changeLevel {S : Scheme.{u}} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {m n : ℕ} (hmn : m = n)
    (t : ℕ) (H G : Fin t → Grp (Over S)) (i : ∀ v, H v ⟶ G v)
    (e : Assembly.Construction.torsionGroup A n ≅ BlockProducts.Construction.groupBlockProduct t G) :
    Assembly.Construction.fullKernelToAbelian A m t H G i (eqToIso (congrArg (Assembly.Construction.torsionGroup A) hmn) ≪≫ e) =
      Assembly.Construction.fullKernelToAbelian A n t H G i e := by
  subst n
  simp [Assembly.Construction.fullKernelToAbelian, BlockProducts.Construction.fullBlockKernelInclusion]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AssemblyTransport.Construction
