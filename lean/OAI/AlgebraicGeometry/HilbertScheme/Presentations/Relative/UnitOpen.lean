import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OpenUnitLocus

/-! # Unit Open -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.UnitOpen

noncomputable section

/-! Principal-open representability in the category of schemes over a base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) (s : Γ(M.left, ⊤))

def relativeUnitOpen : Over S :=
  Over.mk ((M.left.basicOpen s).ι ≫ M.hom)

def relativeUnitOpenInclusion : relativeUnitOpen M s ⟶ M :=
  Over.homMk (M.left.basicOpen s).ι rfl

instance relativeUnitOpenInclusion_isOpenImmersion :
    IsOpenImmersion (relativeUnitOpenInclusion M s).left := inferInstanceAs
  (IsOpenImmersion (M.left.basicOpen s).ι)

theorem relativeUnitOpenInclusion_isUnit :
    IsUnit ((relativeUnitOpenInclusion M s).left.appTop s) := by
  apply (OpenUnitLocus.isUnit_appTop_iff_range_subset _ _).mpr
  change Set.range (M.left.basicOpen s).ι ⊆ (M.left.basicOpen s : Set M.left)
  rw [Scheme.Opens.range_ι]

def relativeUnitSubfunctor : Subfunctor (yoneda.obj M) where
  obj _T := {f | IsUnit (f.left.appTop s)}
  map a _f hf := hf.map a.unop.left.appTop.hom

def relativeUnitOpenPointEquiv (T : Over S) :
    (T ⟶ relativeUnitOpen M s) ≃ {f : T ⟶ M // IsUnit (f.left.appTop s)} where
  toFun f := ⟨f ≫ relativeUnitOpenInclusion M s,
    (relativeUnitOpenInclusion_isUnit M s).map f.left.appTop.hom⟩
  invFun f :=
    let h : Set.range f.val.left ⊆ Set.range (M.left.basicOpen s).ι := by
      rw [Scheme.Opens.range_ι]
      exact (OpenUnitLocus.isUnit_appTop_iff_range_subset _ _).mp f.property
    let g : T.left ⟶ (M.left.basicOpen s).toScheme :=
      IsOpenImmersion.lift (M.left.basicOpen s).ι f.val.left h
    Over.homMk g (by
      change g ≫ (M.left.basicOpen s).ι ≫ M.hom = T.hom
      dsimp only [g]
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact f.val.w)
  left_inv f := by
    apply (Over.forget S).map_injective
    apply (cancel_mono (M.left.basicOpen s).ι).mp
    exact IsOpenImmersion.lift_fac _ _ _
  right_inv f := by
    apply Subtype.ext
    apply (Over.forget S).map_injective
    have h : Set.range f.val.left ⊆ Set.range (M.left.basicOpen s).ι := by
      rw [Scheme.Opens.range_ι]
      exact (OpenUnitLocus.isUnit_appTop_iff_range_subset _ _).mp f.property
    exact IsOpenImmersion.lift_fac (M.left.basicOpen s).ι f.val.left h

def relativeUnitOpenRepresentation :
    yoneda.obj (relativeUnitOpen M s) ≅ (relativeUnitSubfunctor M s).toFunctor :=
  NatIso.ofComponents (fun T => (relativeUnitOpenPointEquiv M s T.unop).toIso) (by
    intro T U a
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact Category.assoc _ _ _)

theorem relativeUnitOpenRepresentation_inclusion :
    (relativeUnitOpenRepresentation M s).hom ≫ (relativeUnitSubfunctor M s).ι =
      yoneda.map (relativeUnitOpenInclusion M s) := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.UnitOpen
