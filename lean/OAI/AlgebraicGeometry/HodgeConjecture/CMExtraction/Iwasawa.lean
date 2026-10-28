import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Borel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Retraction

/-! # Iwasawa -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Iwasawa

noncomputable section

/-! GL3 Iwasawa height at the literal GL3(Zq) subgroup, with the same
integer valuations as the constructed SL3 transform. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]

def gl3BorelValuation : RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q] →* Multiplicative (Fin 3 → ℤ) where
  toFun b := Multiplicative.ofAdd (fun i => (Borel.Iwasawa.unitValuation q (RepresentationTheory.Satake.GL3GL.Core.diagonal ℚ_[q] b i)).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' b c := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg Multiplicative.toAdd (by
      change Borel.Iwasawa.unitValuation q (RepresentationTheory.Satake.GL3GL.Core.diagonal ℚ_[q] (b * c) i) = _
      rw [map_mul]
      exact (Borel.Iwasawa.unitValuation q).map_mul _ _)

theorem gl3BorelValuation_apply (b : RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q]) (i : Fin 3) :
    (gl3BorelValuation q b).toAdd i = (b.val.val i i).valuation := rfl

theorem gl3_compact_borel_valuation (b : RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q])
    (hb : b.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) : gl3BorelValuation q b = 1 := by
  obtain ⟨U, hU⟩ := hb
  have htri : U.val.IsUpperTriangular := by
    intro i j hij
    apply Subtype.val_injective
    change (↑(U.val i j) : ℚ_[q]) = 0
    have h : b.val.val i j = 0 := b.property hij
    rw [← hU] at h
    exact h
  have hunit (i : Fin 3) : IsUnit (U.val i i) := by
    have hdet := U.det.isUnit
    change IsUnit U.val.det at hdet
    rw [Matrix.det_of_isUpperTriangular htri] at hdet
    exact (IsUnit.prod_univ_iff.mp hdet) i
  apply Multiplicative.toAdd.injective
  funext i
  rw [gl3BorelValuation_apply]
  change (b.val.val i i).valuation = 0
  rw [← hU]
  exact Borel.Iwasawa.padic_valuation_zero_of_norm_one q _ (PadicInt.isUnit_iff.mp (hunit i))

def gl3Decomposition : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (Fin 3 → ℤ) where
  B := RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q]
  valuation := gl3BorelValuation q
  compact_valuation := gl3_compact_borel_valuation q
  factorization g := by
    obtain ⟨U, hU⟩ := PadicIntegralCoordinates.Iwasawa.integralGL_reduction q g
    let u := PadicIntegralCoordinates.Iwasawa.integralGLMap q U
    refine ⟨⟨g * u, hU⟩, ⟨u⁻¹, (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q).inv_mem ⟨U, rfl⟩⟩, ?_⟩
    change g = (g * u) * u⁻¹
    rw [mul_assoc, mul_inv_cancel, mul_one]

def sl3ToGL3Coset : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q →
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q :=
  HeckePushforward.Local.heckeCosetPushforward (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)
    Matrix.SpecialLinearGroup.toGL (fun g hg => (RepresentationTheory.Theta.Geometric.Lattices.Spherical.toGL_integral_iff q g).mpr hg)

theorem gl3_height_sl3 (x : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    (gl3Decomposition q).height (sl3ToGL3Coset q x) = (Borel.Iwasawa.decomposition q).height x := by
  obtain ⟨b, rfl⟩ := (Borel.Iwasawa.decomposition q).exists_representative x
  let b' : (gl3Decomposition q).B := ⟨Matrix.SpecialLinearGroup.toGL b.val, b.property⟩
  exact ((gl3Decomposition q).height_mk b').trans ((Borel.Iwasawa.decomposition q).height_mk b).symm

theorem sl3ToGL3Hecke_kernel {s : ℕ} (v : Fin s) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (Retraction.Local.sl3ToGL3Hecke q v T) =
      Finsupp.mapDomain (sl3ToGL3Coset q) (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T) := by
  change AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)
    (Retraction.Local.activeGL3HeckeRetraction q v
      (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q v (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v) T)) = _
  rw [Retraction.Local.activeGL3HeckeRetraction_kernel, Retraction.Local.canonical_activeHeckeMap_kernel]
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ _) = _
  rw [← Finsupp.mapDomain_comp]
  apply congrArg (fun f => Finsupp.mapDomain f (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T))
  funext c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  change QuotientGroup.mk ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeEmbedding q v g).1 v) =
    QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL g)
  rw [RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeEmbedding_self]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Iwasawa
