import OAI.RepresentationTheory.Theta.Kernel.IntrinsicAnalysis

/-! # Intrinsic Global Lattice -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicGlobalLattice.Intrinsic

noncomputable section

/-! The native support lattice identifies the literal theta sum at
every matrix parameter, not only at positive symmetric matrices. This
gives a genuine ambient extension for local parameter differentiation. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise BoundedContinuousFunction

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def realRationalPosition (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) : Adelic.BallGeometryData.FrameIndex A → ℝ :=
  fun i => (B.rationalPosition x i : ℝ)

theorem realRationalPosition_injective : Function.Injective (realRationalPosition B) := by
  intro x y h
  apply B.rationalPosition.injective
  funext i
  have hi := congrFun h i
  change (B.rationalPosition x i : ℝ) = (B.rationalPosition y i : ℝ) at hi
  exact_mod_cast hi

theorem global_lattice_presentation (hL : Adelic.DataTheta.Descent.LatticeIdentification B) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) :
    ∃ (L : Submodule ℤ (Adelic.BallGeometryData.FrameIndex A → ℝ)) (_ : DiscreteTopology L) (φ : L →ᵇ ℂ),
      (∀ Z ξ, Adelic.DataTheta.rationalTheta B f Z ξ = Definitions.theta L φ Z ξ) ∧
      (∀ Z, Adelic.DataTheta.completedTheta B f Z = Definitions.completedTheta L φ Z) ∧
      ∀ a Z, Adelic.DataTheta.completedTensor B f a Z = Definitions.completedTensor L φ a Z := by
  obtain ⟨L,hLd,φ,hlift,hzero,hφ,_,_⟩ := hL f
  let : DiscreteTopology L := hLd
  choose q hq using hlift
  have hqi : Function.Injective q := by
    intro l k h
    apply Subtype.ext
    exact (hq l).symm.trans ((congrArg (realRationalPosition B) h).trans (hq k))
  have hw (l : L) : Adelic.DataTheta.rationalWeight f (q l) = φ l := by
    have hmem : realRationalPosition B (q l) ∈ L := by
      change (fun i => (B.rationalPosition (q l) i : ℝ)) ∈ L
      rw [hq l]
      exact l.property
    have h := hφ (q l) hmem
    have he : (⟨realRationalPosition B (q l),hmem⟩ : L) = l := Subtype.ext (hq l)
    change φ ⟨realRationalPosition B (q l),hmem⟩ = Adelic.DataTheta.rationalWeight f (q l) at h
    rw [he] at h
    exact h.symm
  have hz (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) (hx : x ∉ Set.range q) : Adelic.DataTheta.rationalWeight f x = 0 := by
    apply hzero
    intro hmem
    apply hx
    refine ⟨⟨realRationalPosition B x,hmem⟩,?_⟩
    apply realRationalPosition_injective B
    exact hq ⟨realRationalPosition B x,hmem⟩
  have he (Z : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) :
      Adelic.DataTheta.rationalTheta B f Z ξ = Definitions.theta L φ Z ξ := by
    have ht (l : L) : Adelic.DataTheta.thetaSummand B f Z ξ (q l) = φ l * Adelic.DataTheta.gaussianValue Z ξ l.val := by
      change Adelic.DataTheta.rationalWeight f (q l) * Adelic.DataTheta.gaussianValue Z ξ (realRationalPosition B (q l)) = _
      rw [hw]
      change φ l * Adelic.DataTheta.gaussianValue Z ξ (fun i => (B.rationalPosition (q l) i : ℝ)) = _
      rw [hq l]
    have hsum := hqi.tsum_eq (f := Adelic.DataTheta.thetaSummand B f Z ξ) (fun x hx => by
      by_contra hout
      apply hx
      simp [Adelic.DataTheta.thetaSummand,hz x hout])
    simpa only [Adelic.DataTheta.rationalTheta,Definitions.theta,ht,Adelic.DataTheta.gaussianValue] using hsum.symm
  have hc (Z : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ) :
      Adelic.DataTheta.completedTheta B f Z = Definitions.completedTheta L φ Z := by
    funext ξ
    unfold Adelic.DataTheta.completedTheta Definitions.completedTheta
    rw [he]
  refine ⟨L,hLd,φ,he,hc,?_⟩
  intro a Z
  unfold Adelic.DataTheta.completedTensor Definitions.completedTensor
  rw [hc]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicGlobalLattice.Intrinsic
