import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.ActionComposition
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrbitQuotientExists

/-! # Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Action.FreeConstantAction

/-! Constructing the quotient scheme of a free finite action over an affine morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X : Over S} {G : Type u} [Group G] (d : FreeConstant.FreeConstantAction.Data X G)

theorem jointly_monic_left [Etale X.hom] :
    JointlyMono₂ (FreeConstant.FreeConstantAction.source (X := X) (G := G)).left (FreeConstant.FreeConstantAction.target d).left := by
  constructor
  intro Z f g h₁ h₂
  have hg : g ≫ (FreeConstant.FreeConstantAction.relation (X := X) (G := G)).hom =
      f ≫ (FreeConstant.FreeConstantAction.relation (X := X) (G := G)).hom := by
    rw [← (FreeConstant.FreeConstantAction.source (X := X) (G := G)).w, ← Category.assoc, ← Category.assoc, h₁]
  let f' : Over.mk (f ≫ (FreeConstant.FreeConstantAction.relation (X := X) (G := G)).hom) ⟶ FreeConstant.FreeConstantAction.relation :=
    Over.homMk f rfl
  let g' : Over.mk (f ≫ (FreeConstant.FreeConstantAction.relation (X := X) (G := G)).hom) ⟶ FreeConstant.FreeConstantAction.relation :=
    Over.homMk g hg
  exact congrArg (fun k => k.left) ((FreeConstant.FreeConstantAction.jointly_monic d).right_cancellation f' g'
    (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂))

noncomputable def schemeEquivalenceRelation [Etale X.hom] :
    CategoryTheory.EquivalenceRelation (FreeConstant.FreeConstantAction.source (X := X) (G := G)).left (FreeConstant.FreeConstantAction.target d).left := by
  let e := ActionComposition.FreeConstantAction.equivalenceRelation d
  let : JointlyMono₂ ((Over.forget S).map (FreeConstant.FreeConstantAction.source (X := X) (G := G)))
      ((Over.forget S).map (FreeConstant.FreeConstantAction.target d)) := jointly_monic_left d
  exact
    { __ := e.toReflexiveRelation.map (Over.forget S)
      __ := e.toSymmetricRelation.map (Over.forget S)
      __ := e.toTransitiveRelation.map (Over.forget S) }

/-- The orbit-neighborhood input is automatic for an affine structural map:
the inverse image of any affine neighborhood of the base contains the orbit. -/
theorem affine_orbits [IsAffineHom X.hom] (x : X.left) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧
      ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (FreeConstant.FreeConstantAction.source (X := X) (G := G)).left
        (FreeConstant.FreeConstantAction.target d).left x y → y ∈ U := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (X.hom x))
  refine ⟨X.hom ⁻¹ᵁ V, hV.preimage X.hom, ?_⟩
  rintro y ⟨z, hz, hz'⟩
  have he : X.hom x = X.hom y := by
    have hb := (FreeConstant.FreeConstantAction.source (X := X) (G := G)).w.trans (FreeConstant.FreeConstantAction.target d).w.symm
    simpa only [Scheme.Hom.comp_apply, hz, hz'] using congrArg (fun f => f z) hb
  change X.hom y ∈ V
  exact he ▸ hxV

/-- An actual scheme quotient, constructed from the free action and finite
constant source. Its existence is not an input to this theorem. -/
theorem exists_quotient [Finite G] [Etale X.hom] [IsAffineHom X.hom] :
    ∃ (Q : Over S) (q : X ⟶ Q),
      IsFinite q.left ∧ Flat q.left ∧ LocallyOfFinitePresentation q.left ∧
        Surjective q.left ∧
      IsKernelPair q.left (FreeConstant.FreeConstantAction.source (X := X) (G := G)).left (FreeConstant.FreeConstantAction.target d).left := by
  have ha : (FreeConstant.FreeConstantAction.source (X := X) (G := G)).left ≫ X.hom = (FreeConstant.FreeConstantAction.target d).left ≫ X.hom :=
    (FreeConstant.FreeConstantAction.source (X := X) (G := G)).w.trans (FreeConstant.FreeConstantAction.target d).w.symm
  obtain ⟨Q, π, hf, hfl, hfp, hsurj, hk, hu⟩ :=
    Quotients.FiniteDescent.OrbitQuotientExists.Construction.OrbitQuotient.exists_quotient (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G).hom X.hom
      (ConstantPointsIs.ConstantPoints.map X.hom G) (FreeConstant.FreeConstantAction.source (X := X) (G := G)).left (FreeConstant.FreeConstantAction.target d).left
      (ConstantPointsIs.ConstantPoints.isPullback X.hom G) (schemeEquivalenceRelation d) ha (affine_orbits d)
  obtain ⟨b, hb, _⟩ := hu S X.hom ha
  exact ⟨Over.mk b, Over.homMk π hb, hf, hfl, hfp, hsurj, hk⟩

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Action.FreeConstantAction
