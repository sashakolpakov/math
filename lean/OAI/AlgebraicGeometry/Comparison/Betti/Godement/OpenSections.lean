import OAI.AlgebraicGeometry.Comparison.Betti.ExactFunctorResolution
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueResolutionOpenSections
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Injective

/-! # Open Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.OpenSections

noncomputable section

/-! The actual Godement resolution is exact on every cohomologically acyclic open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (F : FlasqueBiproduct.ComplexSheaves X)

local instance godementForgetAdditive : (Complex.SheafForget.Flasque.sheafForget X).Additive :=
  Complex.SheafForget.Flasque.sheafForgetAdditive X
local instance godementForgetHomology : (Complex.SheafForget.Flasque.sheafForget X).PreservesHomology :=
  Complex.SheafForget.Flasque.sheafForgetPreservesHomology X

def godementAdditiveResolutionData : ResolutionExactImage.Data ((Complex.SheafForget.Flasque.sheafForget X).obj F) :=
  ExactFunctorResolution.mapResolutionData (Complex.SheafForget.Flasque.sheafForget X) (Injective.godementResolutionData F)

theorem godementComplex_openSections_exactAt_succ (V : Opens X)
    (hF : ∀ q, Subsingleton (Sheaf.H.{0}
      ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat V.isOpenEmbedding).obj
        ((Complex.SheafForget.Flasque.sheafForget X).obj F)) (q + 1))) (n : ℕ) :
    (((FlasqueBiproduct.sections V).mapHomologicalComplex (.up ℕ)).obj
      (Resolution.godementComplex X F)).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hfl (p : ℕ) : TopCat.Sheaf.IsFlasque ((godementAdditiveResolutionData F).complex.X p) := by
    have := Resolution.godementComplex_isFlasque X F p
    exact Complex.SheafForget.Flasque.sheafForgetFlasque ((Resolution.godementComplex X F).X p)
  exact FlasqueResolutionOpenSections.flasqueResolution_openSections_exact_succ
    (godementAdditiveResolutionData F) hfl V hF n x hx

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.OpenSections
