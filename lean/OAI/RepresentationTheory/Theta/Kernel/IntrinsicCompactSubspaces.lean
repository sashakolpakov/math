import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison

/-! # Intrinsic Compact Subspaces -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSubspaces.Intrinsic

noncomputable section

/-! Equality of the actual moved Hodge subspaces determines their
period charts. This removes compact frame bases from the parameter. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.IntrinsicGraph
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame

theorem graph_range_injective {I V : Type} [Fintype I] [DecidableEq I]
    (e : ((I ⊕ I) → ℂ) → V) (he : Function.Injective e) (Z W : Matrix I I ℂ)
    (h : Set.range (fun x => e (Sum.elim x (Z.mulVec x))) =
      Set.range (fun x => e (Sum.elim x (W.mulVec x)))) : Z = W := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  obtain ⟨y,hy⟩ := h ▸ (Set.mem_range_self x : e (Sum.elim x (Z.mulVec x)) ∈
    Set.range (fun x => e (Sum.elim x (Z.mulVec x))))
  have hg := he hy
  have hpos : y = x := funext (fun i => congrFun hg (.inl i))
  subst y
  exact (funext (fun i => congrFun hg (.inr i))).symm

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

def movedHodgeSubspace (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (z : Adelic.BallNatural.Ball) : Set (Adelic.BallGeometryData.ComplexPhase A) :=
  Set.range (IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z)

def compactSubspaceSetoid : Setoid (IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) where
  r p q := ∀ z, movedHodgeSubspace A p z = movedHodgeSubspace A q z
  iseqv := ⟨fun _ _ => rfl,fun h z => (h z).symm,fun h k z => (h z).trans (k z)⟩

def CompactLagrangianChoice := Quotient (compactSubspaceSetoid A)

instance : TopologicalSpace (CompactLagrangianChoice A) :=
  inferInstanceAs (TopologicalSpace (Quotient (compactSubspaceSetoid A)))

variable {A} (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem physical_action_graph (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    B.complexPhase (Sum.elim ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec a)
      ((IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec
        ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec a))) = IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z a := by
  have hg := IntrinsicCompactFrameComparison.IntrinsicGraph.parameter_chart_graph B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p) z
    (IntrinsicCompactFrameComparison.Intrinsic.action_parameter_graph_domain p B Bp hC hCp hG hGp z) a
  exact (congrArg B.complexPhase
    (hg.symm.trans (IntrinsicCompactActionParameter.Intrinsic.coordinate_action_frame A B hG p z a))).trans (B.complexPhase.apply_symm_apply _)

theorem moved_hodge_graph_range (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    Set.range (fun x => B.complexPhase
      (Sum.elim x ((IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec x))) =
      movedHodgeSubspace A p z := by
  ext w
  constructor
  · rintro ⟨x,rfl⟩
    let M : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ := IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)
    have hx : M.mulVec (M⁻¹.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
        (isUnit_iff_ne_zero.mpr (IntrinsicCompactFrameComparison.Intrinsic.compact_frame_det_nonzero p B Bp hC hCp hG hGp z)),Matrix.one_mulVec]
    refine ⟨M⁻¹.mulVec x,?_⟩
    have h := physical_action_graph p B Bp hC hCp hG hGp z (M⁻¹.mulVec x)
    change B.complexPhase (Sum.elim (M.mulVec (M⁻¹.mulVec x))
      ((IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec (M.mulVec (M⁻¹.mulVec x)))) = _ at h
    rw [hx] at h
    exact h.symm
  · rintro ⟨a,rfl⟩
    exact ⟨(IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec a,
      physical_action_graph p B Bp hC hCp hG hGp z a⟩

theorem same_subspace_period (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (q : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (Bq : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A q)) (hCq : Adelic.DataTheta.CoordinateIdentification Bq P)
    (hGq : Adelic.DataTheta.GeometryIdentification Bq) (z : Adelic.BallNatural.Ball)
    (he : movedHodgeSubspace A p z = movedHodgeSubspace A q z) :
    IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) = IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A q,z.val) :=
  graph_range_injective B.complexPhase B.complexPhase.injective _ _
    ((moved_hodge_graph_range p B Bp hC hCp hG hGp z).trans
      (he.trans (moved_hodge_graph_range q B Bq hC hCq hG hGq z).symm))

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSubspaces.Intrinsic
