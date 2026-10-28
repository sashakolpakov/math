import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ConstantScheme
import OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleSectionIso

/-! # Connected Constant Cover -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ConnectedConstantCover.Construction

noncomputable section

/-! A connected nonempty finite etale subcover of a constant cover has degree one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- A map from a connected nonempty scheme into a constant scheme lies in one copy of the base. -/
theorem connected_constantScheme_map_factor {S T : Scheme.{u}} [PreconnectedSpace T] [Nonempty T]
    (I : Type u) (f : T ⟶ S) (a : Over.mk f ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I) :
    ∃ i : I, a.left = f ≫ Sigma.ι (fun _ : I => S) i := by
  have : PreconnectedSpace (Over.mk f).left := inferInstanceAs (PreconnectedSpace T)
  let x : T := Nonempty.some inferInstance
  let c := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (Over.mk f) a
  let i := c x
  let b : Over.mk f ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I := Over.homMk (f ≫ Sigma.ι (fun _ : I => S) i) (by simp)
  have hc : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (Over.mk f) b = LocallyConstant.const T i := by
    ext y
    exact AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i (f y)
  have hab : a = b := (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I (Over.mk f)).injective
    ((c.eq_const x).trans hc.symm)
  exact ⟨i, congrArg (fun z : Over.mk f ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I => z.left) hab⟩

/-- A monomorphic finite etale map with nonempty source onto a connected base is an isomorphism. -/
theorem finite_etale_mono_isIso_of_nonempty {X Y : Scheme.{u}}
    [PreconnectedSpace Y] [IsReduced Y] [Nonempty X]
    (f : X ⟶ Y) [IsFinite f] [Etale f] [Mono f] : IsIso f := by
  have : IsClosedImmersion f := (IsClosedImmersion.iff_isFinite_and_mono f).mpr ⟨inferInstance, inferInstance⟩
  have hcl : IsClopen (Set.range f) := ⟨f.isClosedEmbedding.isClosed_range, f.isOpenMap.isOpen_range⟩
  have hr : Set.range f = Set.univ := hcl.eq_univ (Set.range_nonempty f)
  have : Surjective f := ⟨Set.range_eq_univ.mp hr⟩
  exact isIso_of_isClosedImmersion_of_surjective f

/-- A connected nonempty finite etale cover admitting a monomorphism into a constant cover is trivial. -/
theorem connected_finiteEtale_subconstant_isIso {S T : Scheme.{u}}
    [PreconnectedSpace S] [IsReduced S] [PreconnectedSpace T] [Nonempty T]
    (I : Type u) (f : T ⟶ S) [IsFinite f] [Etale f]
    (a : Over.mk f ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I) [Mono a.left] : IsIso f := by
  obtain ⟨i, hi⟩ := connected_constantScheme_map_factor I f a
  have : Mono (f ≫ Sigma.ι (fun _ : I => S) i) := hi ▸ inferInstance
  have : Mono f := mono_of_mono f (Sigma.ι (fun _ : I => S) i)
  exact finite_etale_mono_isIso_of_nonempty f

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ConnectedConstantCover.Construction
