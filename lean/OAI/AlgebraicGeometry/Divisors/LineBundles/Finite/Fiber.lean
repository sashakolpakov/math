import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.FiberPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericRegularFunction

/-! # Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.Fiber.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual zero fibers and finiteness after pullback -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem finiteMorphism_noetherian {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f]
    [AlgebraicGeometry.IsNoetherian Y] : AlgebraicGeometry.IsNoetherian X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

theorem pullbackClosed_zeroFiber {X Y Z : Scheme.{0}} (i : X ⟶ Y) (j : Z ⟶ Y)
    (a : Γ(Y, ⊤)) (hzero : Set.range j = (Y.basicOpen a : Set Y)ᶜ) :
    Set.range (pullback.fst i j) = (X.basicOpen (i.appTop a) : Set X)ᶜ := by
  rw [Scheme.Pullback.range_fst, hzero]
  exact congrArg (fun U : X.Opens => (U : Set X)ᶜ) (Scheme.preimage_basicOpen_top i a)

theorem genericPullback_globalSection_ne_zero {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (i : X ⟶ Y) (hη : i (genericPoint X) = genericPoint Y) (a : Γ(Y, ⊤)) (ha : a ≠ 0) :
    i.appTop a ≠ 0 := by
  have hg : Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη (RegularDivisor.BundleCycles.globalFunctionFieldElement Y a) ≠ 0 :=
    (map_ne_zero_iff (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη).hom
      (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη).hom.injective).mpr (RegularDivisor.BundleCycles.globalFunctionFieldElement_ne_zero Y a ha)
  intro h
  apply hg
  rw [GenericRegularFunction.BundleCycles.genericFieldMap_globalFunction i hη a, h]
  exact map_zero (X.germToFunctionField ⊤).hom

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.Fiber.BundleCycles
