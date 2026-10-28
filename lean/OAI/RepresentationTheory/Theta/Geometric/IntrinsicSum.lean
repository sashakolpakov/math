import OAI.RepresentationTheory.Theta.Geometric.KernelSum
import OAI.RepresentationTheory.Theta.Geometric.Active.DoubleCosetFibers
import OAI.RepresentationTheory.Theta.Geometric.Away
import OAI.RepresentationTheory.Theta.Geometric.Data
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Hecke

/-! # Intrinsic Sum -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Geometric.IntrinsicSum.Spherical

/-! Any rational representatives of the original raw cosets give the
same finite Weil sum when their full away components preserve the level. -/

variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module ℂ V]
    (K : Subgroup G) (L : Subgroup A) (rho : G × A →* (V ≃ₗ[ℂ] V))

theorem productInverseWeil_cosetValue (φ : SphericalGU.Spherical.fixedInputs (K.prod L) rho)
    (r : G × A) (c : G ⧸ K) (hc : (QuotientGroup.mk r.1⁻¹ : G ⧸ K) = c)
    (ha : r.2 ∈ L) :
    rho r⁻¹ φ.val = SphericalGU.Spherical.cosetValue K (rho.comp (MonoidHom.inl G A))
      ⟨φ.val, ((Away.Spherical.fixedProduct_iff K L rho φ.val).mp φ.property).1⟩ c := by
  have hlocal : r.1 * c.out ∈ K := by
    have h := QuotientGroup.eq.mp (hc.trans (QuotientGroup.out_eq' c).symm)
    simpa only [inv_inv] using h
  have hprod : (QuotientGroup.mk r⁻¹ : (G × A) ⧸ K.prod L) =
      QuotientGroup.mk (c.out, 1) := by
    apply QuotientGroup.eq.mpr
    rw [inv_inv]
    change r.1 * c.out ∈ K ∧ r.2 * 1 ∈ L
    exact ⟨hlocal, by rw [mul_one]; exact ha⟩
  refine (SphericalGU.Spherical.weil_value_eq_of_same_coset (K.prod L) rho φ hprod).trans ?_
  conv_rhs => rw [← QuotientGroup.out_eq' c]
  rfl

variable [Module ℚ V] [IsScalarTower ℚ ℂ V]

theorem productWeilAction_raw_representatives (a : G) (T : SphericalGU.Spherical.algebra K)
    (hT : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset K a T) [Fintype (DoubleCosets.Spherical.DoubleCosetFiber K a⁻¹)]
    (r : DoubleCosets.Spherical.DoubleCosetFiber K a⁻¹ → G × A)
    (hc : ∀ c, (QuotientGroup.mk (r c).1⁻¹ : G ⧸ K) = c.val)
    (ha : ∀ c, (r c).2 ∈ L) (φ : SphericalGU.Spherical.fixedInputs (K.prod L) rho) :
    (Away.Spherical.productWeilAction K L rho T φ).val =
      ∑ c : DoubleCosets.Spherical.DoubleCosetFiber K a⁻¹, rho (r c)⁻¹ φ.val := by
  classical
  let e := Active.DoubleCosetFibers.Spherical.rawSupportDoubleCosetEquiv K a
  let : Fintype (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport K a) := Fintype.ofEquiv (DoubleCosets.Spherical.DoubleCosetFiber K a⁻¹) e.symm
  rw [Away.Spherical.productWeilAction_val]
  change (SphericalGU.Spherical.kernel K T).sum (fun c b => b • SphericalGU.Spherical.cosetValue K (rho.comp (MonoidHom.inl G A))
    ⟨φ.val, ((Away.Spherical.fixedProduct_iff K L rho φ.val).mp φ.property).1⟩ c) = _
  rw [KernelSum.rawKernel_sum K a T hT]
  rw [← e.sum_comp (fun c : DoubleCosets.Spherical.DoubleCosetFiber K a⁻¹ => rho (r c)⁻¹ φ.val)]
  apply Finset.sum_congr rfl
  intro c _
  exact (productInverseWeil_cosetValue K L rho φ (r (e c)) (e c).val (hc (e c)) (ha (e c))).symm

end RepresentationTheory.Theta.Geometric.IntrinsicSum.Spherical

namespace RepresentationTheory.Theta.Geometric

/-! Rational theta covariance converts every original raw branch sum
to the finite Weil Hecke action, retaining the complete away marking. -/

set_option backward.isDefEq.respectTransparency false

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.rationalTheta_inverse (ha : D.HasRationalThetaCovariance)
    (g : D.RationalSU) (φ : PoissonAutomorphyNormalizationData.finiteSchwartz Index) (x : D.domain) :
    (D.thetaUniversal φ (D.periodMap g x.val)).comp (fderiv ℂ (D.periodMap g) x.val) =
      D.thetaUniversal (D.finiteWeil ((D.rationalFinite g)⁻¹) φ) x.val := by
  have h := ha g (D.finiteWeil ((D.rationalFinite g)⁻¹) φ) x
  simp only [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact h

theorem Data.ActiveHeckeThetaData.sphericalWeil_raw_representatives
    (w : Intrinsic.Hecke.ActiveWeight) (T : SphericalGU.Spherical.SL3Hecke q)
    (hT : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q w) T)
    {I : Type} [Fintype I] (β : I ≃ Intrinsic.Hecke.activeCosets q w) (g : I → D.RationalSU)
    (hc : ∀ i, (QuotientGroup.mk (D.activeLocal (g i))⁻¹ :
      SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) = (β i).val)
    (ha : ∀ i, D.away (g i) ∈ D.awayLevel) (φ : D.sphericalInputs) :
    (D.sphericalWeil T φ).val =
      ∑ i : I, D.finiteWeil ((D.rationalFinite (g i))⁻¹) φ.val := by
  classical
  let : Fintype (Intrinsic.Hecke.activeCosets q w) := Fintype.ofEquiv I β
  have h := IntrinsicSum.Spherical.productWeilAction_raw_representatives
    (SphericalGU.Spherical.integralSL3 q) D.awayLevel.toSubgroup D.finiteWeil
    (Intrinsic.Hecke.activeSLRepresentative q w) T hT (fun c => D.rationalFinite (g (β.symm c)))
    (fun c => (hc (β.symm c)).trans (congrArg Subtype.val (β.apply_symm_apply c)))
    (fun c => ha (β.symm c)) φ
  change (D.sphericalWeil T φ).val = _ at h
  refine h.trans ?_
  exact (β.symm.sum_comp (fun i => D.finiteWeil ((D.rationalFinite (g i))⁻¹) φ.val))

theorem Data.ActiveHeckeThetaData.native_raw_theta_sum (hautomorphy : D.HasRationalThetaCovariance)
    (w : Intrinsic.Hecke.ActiveWeight) (T : SphericalGU.Spherical.SL3Hecke q)
    (hT : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q w) T)
    {I : Type} [Fintype I] (β : I ≃ Intrinsic.Hecke.activeCosets q w) (g : I → D.RationalSU)
    (hc : ∀ i, (QuotientGroup.mk (D.activeLocal (g i))⁻¹ :
      SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) = (β i).val)
    (ha : ∀ i, D.away (g i) ∈ D.awayLevel) (φ : D.sphericalInputs)
    (x : D.domain) (u : LinearTheta.BallCoordinates) :
    (∑ i : I, D.thetaUniversal φ.val (D.periodMap (g i) x.val)
      (fderiv ℂ (D.periodMap (g i)) x.val u)) =
      D.thetaUniversal (D.sphericalWeil T φ).val x.val u := by
  have h := congrArg (fun f : PoissonAutomorphyNormalizationData.finiteSchwartz Index => D.thetaUniversal f x.val u)
    (D.sphericalWeil_raw_representatives w T hT β g hc ha φ)
  simp only [map_sum, Finset.sum_apply, sum_apply] at h
  change D.thetaUniversal (D.sphericalWeil T φ).val x.val u =
    ∑ i : I, D.thetaUniversal (D.finiteWeil ((D.rationalFinite (g i))⁻¹) φ.val) x.val u at h
  refine (Finset.sum_congr rfl (fun i _ => ?_)).trans h.symm
  exact congrArg (fun a : LinearTheta.Cotangent => a u) (D.rationalTheta_inverse hautomorphy (g i) φ.val x)

end RepresentationTheory.Theta.Geometric

end

end OAI
