import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedSectionsEq

/-! # Pullback Coherence -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PullbackCoherence

noncomputable section

/-! Native pullback of module morphisms respects composition and can
be detected on any open cover. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
universe u

theorem nativePullback_nested {X Y T U V : Scheme.{u}} {M : X.Modules} {N : Y.Modules}
    {x : T ⟶ X} {y : T ⟶ Y}
    (φ : (Scheme.Modules.pullback x).obj M ⟶ (Scheme.Modules.pullback y).obj N)
    (r : U ⟶ T) (x' : U ⟶ X) (y' : U ⟶ Y) (hx : r ≫ x = x') (hy : r ≫ y = y')
    (s : V ⟶ U) (x'' : V ⟶ X) (y'' : V ⟶ Y)
    (hx' : s ≫ x' = x'') (hy' : s ≫ y' = y'') :
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback (AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback φ r x' y' hx hy) s x'' y'' hx' hy' =
      AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback φ (s ≫ r) x'' y''
        (by rw [Category.assoc, hx, hx']) (by rw [Category.assoc, hy, hy']) := by
  have h := pullHom_pullHom (F := AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) φ r x' y' s x'' y'' hx hy hx' hy'
  simpa only [AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback, AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom.pullHom_eq] using h

theorem nativePullback_comp {X Y Z T U : Scheme.{u}}
    {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
    {x : T ⟶ X} {y : T ⟶ Y} {z : T ⟶ Z}
    (φ : (Scheme.Modules.pullback x).obj M ⟶ (Scheme.Modules.pullback y).obj N)
    (ψ : (Scheme.Modules.pullback y).obj N ⟶ (Scheme.Modules.pullback z).obj P)
    (r : U ⟶ T) (x' : U ⟶ X) (y' : U ⟶ Y) (z' : U ⟶ Z)
    (hx : r ≫ x = x') (hy : r ≫ y = y') (hz : r ≫ z = z') :
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback (φ ≫ ψ) r x' z' hx hz =
      AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback φ r x' y' hx hy ≫ AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback ψ r y' z' hy hz := by
  have h := AlgebraicGeometry.Picard.PoincareBundle.PullHom.pullHom_comp (F := AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) φ ψ r x' y' z' hx hy hz
  simpa only [AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback, AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom.pullHom_eq] using h

theorem nativePullback_ext_open_cover {X Y T : Scheme.{u}} {M : X.Modules} {N : Y.Modules}
    {x : T ⟶ X} {y : T ⟶ Y}
    (φ ψ : (Scheme.Modules.pullback x).obj M ⟶ (Scheme.Modules.pullback y).obj N)
    {I : Type u} (U : I → T.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback φ (U i).ι ((U i).ι ≫ x) ((U i).ι ≫ y) rfl rfl =
      AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback ψ (U i).ι ((U i).ι ≫ x) ((U i).ι ≫ y) rfl rfl) : φ = ψ := by
  apply AlgebraicGeometry.Quotients.FiniteDescent.ReducedSectionsEq.Construction.ReducedSections.moduleMap_eq_of_locally
  intro t
  have ht : t ∈ iSup U := hU.symm ▸ (show t ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
  refine ⟨U i, hi, ?_⟩
  apply (cancel_epi ((Scheme.Modules.pullbackComp (U i).ι x).app M).inv).mp
  apply (cancel_mono ((Scheme.Modules.pullbackComp (U i).ι y).app N).hom).mp
  exact h i

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PullbackCoherence
