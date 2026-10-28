import OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Siegel Square Root -/

namespace OAI.RepresentationTheory.Theta.Adelic.SiegelSquareRoot

noncomputable section

/-! Holomorphic, jointly continuous determinant roots on the whole
Siegel domain, normalized by a continuous value at a fixed period. -/

open scoped Classical _root_.Matrix.Norms.Elementwise

open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

variable {I : Type} [Fintype I] [DecidableEq I]

def siegelRootExtension (f : PoissonAutomorphyNormalizationData.Domain I → ℂ) (M : Matrix I I ℂ) : ℂ :=
  if hM : M ∈ PoissonAutomorphyNormalizationData.siegelSet I then f ⟨M, hM⟩ else 0

theorem continuous_siegel_root_holomorphic (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I ℝ)
    (f : PoissonAutomorphyNormalizationData.Domain I → ℂ) (hf : Continuous f)
    (hs : ∀ Z, f Z ^ 2 = PoissonAutomorphyNormalizationData.denominatorDet g Z) :
    DifferentiableOn ℂ (siegelRootExtension f) (PoissonAutomorphyNormalizationData.siegelSet I) := by
  let c := f (PoissonAutomorphyNormalizationData.basePeriod I) / PoissonAutomorphyNormalizationData.halfDetDomain g (PoissonAutomorphyNormalizationData.basePeriod I)
  have hc : c ^ 2 = 1 := by
    dsimp [c]
    rw [div_pow, hs, PoissonAutomorphyNormalizationData.halfDetDomain_sq, div_self (PoissonAutomorphyNormalizationData.denominatorDet_ne_zero g _)]
  have hn (Z : PoissonAutomorphyNormalizationData.Domain I) : f Z ≠ 0 := by
    intro h
    have he := hs Z
    rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at he
    exact PoissonAutomorphyNormalizationData.denominatorDet_ne_zero g Z he.symm
  have he : f = fun Z => c * PoissonAutomorphyNormalizationData.halfDetDomain g Z := ContinuousSquareRoot.continuous_square_roots_eq f _ hf
    (continuous_const.mul (PoissonAutomorphyNormalizationData.halfDetDomain_continuous g)) hn (fun Z => by
      rw [mul_pow, hc, one_mul, hs, PoissonAutomorphyNormalizationData.halfDetDomain_sq]) (PoissonAutomorphyNormalizationData.basePeriod I) (by
        dsimp [c]
        have hh : PoissonAutomorphyNormalizationData.halfDetDomain g (PoissonAutomorphyNormalizationData.basePeriod I) ≠ 0 := Complex.exp_ne_zero _
        exact (div_mul_cancel₀ _ hh).symm)
  have hext : siegelRootExtension f = fun M => c * PoissonAutomorphyNormalizationData.halfDetExtension g M := by
    funext M
    by_cases hM : M ∈ PoissonAutomorphyNormalizationData.siegelSet I
    · simpa only [siegelRootExtension, PoissonAutomorphyNormalizationData.halfDetExtension, dite_eq_left hM] using congrFun he ⟨M, hM⟩
    · simp only [siegelRootExtension, PoissonAutomorphyNormalizationData.halfDetExtension, dite_eq_right hM, mul_zero]
  rw [hext]
  exact (differentiableOn_const (c := c)).mul (PoissonAutomorphyNormalizationData.halfDetExtension_differentiableOn g)

theorem siegel_parameter_square_root {G : Type*} [TopologicalSpace G]
    (σ : G → AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I ℝ)
    (hC : Continuous (fun g => (σ g).C)) (hD : Continuous (fun g => (σ g).D))
    (Z₀ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (a : G → ℂ) (ha : Continuous a)
    (hs : ∀ g, a g ^ 2 = ((σ g).complexify.denominator Z₀.matrix).det) :
    ∃ J : G → Matrix I I ℂ → ℂ,
      (∀ g, DifferentiableOn ℂ (J g) (PoissonAutomorphyNormalizationData.siegelSet I)) ∧
      ContinuousOn (fun p : G × Matrix I I ℂ => J p.1 p.2) (Set.univ ×ˢ PoissonAutomorphyNormalizationData.siegelSet I) ∧
      (∀ g (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I), J g Z.matrix ≠ 0 ∧
        J g Z.matrix ^ 2 = ((σ g).complexify.denominator Z.matrix).det) ∧
      (∀ g, J g Z₀.matrix = a g) := by
  let determinant : G × PoissonAutomorphyNormalizationData.Domain I → ℂ := fun p => PoissonAutomorphyNormalizationData.denominatorDet (σ p.1) p.2
  have hd : Continuous determinant := by
    change Continuous (fun p : G × PoissonAutomorphyNormalizationData.Domain I =>
      (((σ p.1).C.map Complex.ofRealHom) * p.2.val + (σ p.1).D.map Complex.ofRealHom).det)
    have hc : Continuous (fun g => (σ g).C.map Complex.ofRealHom) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact Complex.continuous_ofReal.comp ((continuous_apply j).comp ((continuous_apply i).comp hC))
    have hd : Continuous (fun g => (σ g).D.map Complex.ofRealHom) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact Complex.continuous_ofReal.comp ((continuous_apply j).comp ((continuous_apply i).comp hD))
    exact (((hc.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).add
      (hd.comp continuous_fst)).matrix_det
  obtain ⟨j, hj, hjs, hja⟩ := ContinuousSquareRoot.parameter_square_root (PoissonAutomorphyNormalizationData.siegelSet I) PoissonAutomorphyNormalizationData.siegelSet_convex (PoissonAutomorphyNormalizationData.ofSiegel Z₀)
    determinant hd (fun p => PoissonAutomorphyNormalizationData.denominatorDet_ne_zero (σ p.1) p.2) a ha hs
  let J : G → Matrix I I ℂ → ℂ := fun g => siegelRootExtension (fun Z => j (g, Z))
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · intro g
    exact continuous_siegel_root_holomorphic (σ g) _
      (hj.comp (continuous_const.prodMk continuous_id)) (fun Z => hjs (g, Z))
  · rw [continuousOn_iff_continuous_domRestrict]
    let embed : (Set.univ ×ˢ PoissonAutomorphyNormalizationData.siegelSet I : Set (G × Matrix I I ℂ)) → G × PoissonAutomorphyNormalizationData.Domain I :=
      fun p => (p.val.1, ⟨p.val.2, p.property.2⟩)
    have he : Continuous embed := by fun_prop
    apply (hj.comp he).congr
    intro p
    change j (p.val.1, ⟨p.val.2, p.property.2⟩) = J p.val.1 p.val.2
    dsimp only [J, siegelRootExtension]
    rw [dite_eq_left p.property.2]
  · intro g Z
    have hZ : Z.matrix ∈ PoissonAutomorphyNormalizationData.siegelSet I := ⟨Z.symmetric, Z.imaginary_posDef⟩
    have hsq : J g Z.matrix ^ 2 = ((σ g).complexify.denominator Z.matrix).det := by
      simpa only [J, siegelRootExtension, dite_eq_left hZ, PoissonAutomorphyNormalizationData.ofSiegel, determinant, PoissonAutomorphyNormalizationData.denominatorDet]
        using hjs (g, PoissonAutomorphyNormalizationData.ofSiegel Z)
    refine ⟨?_, hsq⟩
    intro hz
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsq
    exact (σ g).denominator_det_isUnit Z |>.ne_zero hsq.symm
  · intro g
    have hZ : Z₀.matrix ∈ PoissonAutomorphyNormalizationData.siegelSet I := ⟨Z₀.symmetric, Z₀.imaginary_posDef⟩
    simpa only [J, siegelRootExtension, dite_eq_left hZ, PoissonAutomorphyNormalizationData.ofSiegel] using hja g

end

end OAI.RepresentationTheory.Theta.Adelic.SiegelSquareRoot
