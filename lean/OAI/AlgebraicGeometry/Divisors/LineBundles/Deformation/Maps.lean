import OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiber

/-! # Maps -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps.BundleCycles

noncomputable section

/-!
# LineBundleCycles: functoriality of affine deformation and its special fiber

A homomorphism carrying I into J induces the coefficientwise maps on the
Rees and extended Rees algebras. The resulting normal-cone and special-fiber
maps commute with the canonical special-fiber identification.
-/

universe u v w
variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]

theorem map_idealPower_mem (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (n : ℕ) {r : R} (hr : r ∈ I ^ n) : f r ∈ J ^ n := by
  have h := Ideal.mem_map_of_mem f hr
  rw [Ideal.map_pow] at h
  exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hf) n h

/-- Coefficientwise map of extended Rees algebras. -/
def deformationMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) : Iff.BundleCycles.deformationAlgebra I →+* Iff.BundleCycles.deformationAlgebra J where
  toFun p := ⟨AddMonoidAlgebra.mapRingHom ℤ f p.val, fun n => by
    rw [AddMonoidAlgebra.coeff_mapRingHom]
    exact map_idealPower_mem I J f hf _ (p.property n)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' p q := Subtype.ext (map_add _ p.val q.val)
  map_mul' p q := Subtype.ext (map_mul _ p.val q.val)

@[simp]
theorem deformationMap_coeff (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (p : Iff.BundleCycles.deformationAlgebra I) (n : ℤ) :
    (deformationMap I J f hf p).val.coeff n = f (p.val.coeff n) :=
  AddMonoidAlgebra.coeff_mapRingHom f p.val n

@[simp]
theorem deformationMap_parameter (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    deformationMap I J f hf (Iff.BundleCycles.deformationParameter I) = Iff.BundleCycles.deformationParameter J := by
  apply Subtype.ext
  change AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.single 1 1) =
    AddMonoidAlgebra.single 1 1
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

theorem deformationMap_id (I : Ideal R) :
    deformationMap I I (RingHom.id R) (by intro r hr; exact hr) =
      RingHom.id (Iff.BundleCycles.deformationAlgebra I) := by
  ext p n
  exact deformationMap_coeff I I _ _ p n

theorem deformationMap_comp (I : Ideal R) (J : Ideal S) (K : Ideal A)
    (f : R →+* S) (g : S →+* A) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    (deformationMap J K g hg).comp (deformationMap I J f hf) =
      deformationMap I K (g.comp f) (fun _r hr => hg (hf hr)) := by
  ext p n
  exact ((deformationMap_coeff J K g hg _ n).trans
    (congrArg g (deformationMap_coeff I J f hf p n))).trans
      (deformationMap_coeff I K (g.comp f) (fun _r hr => hg (hf hr)) p n).symm

/-- Coefficientwise map of ordinary Rees algebras. -/
def reesMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) : reesAlgebra I →+* reesAlgebra J where
  toFun p := ⟨p.val.map f, fun n => by
    rw [Polynomial.coeff_map]
    exact map_idealPower_mem I J f hf n (p.property n)⟩
  map_zero' := Subtype.ext (map_zero (Polynomial.mapRingHom f))
  map_one' := Subtype.ext (map_one (Polynomial.mapRingHom f))
  map_add' p q := Subtype.ext (map_add (Polynomial.mapRingHom f) p.val q.val)
  map_mul' p q := Subtype.ext (map_mul (Polynomial.mapRingHom f) p.val q.val)

@[simp]
theorem reesMap_coeff (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (p : reesAlgebra I) (n : ℕ) :
    (reesMap I J f hf p).val.coeff n = f (p.val.coeff n) := Polynomial.coeff_map ..

theorem reesMap_id (I : Ideal R) :
    reesMap I I (RingHom.id R) (by intro r hr; exact hr) = RingHom.id (reesAlgebra I) := by
  ext p n
  exact reesMap_coeff I I _ _ p n

theorem reesMap_comp (I : Ideal R) (J : Ideal S) (K : Ideal A)
    (f : R →+* S) (g : S →+* A) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    (reesMap J K g hg).comp (reesMap I J f hf) =
      reesMap I K (g.comp f) (fun _r hr => hg (hf hr)) := by
  ext p n
  exact ((reesMap_coeff J K g hg _ n).trans
    (congrArg g (reesMap_coeff I J f hf p n))).trans
      (reesMap_coeff I K (g.comp f) (fun _r hr => hg (hf hr)) p n).symm

/-- Exponent reversal commutes with every coefficient homomorphism. -/
theorem deformationMap_reesToDeformation (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (p : reesAlgebra I) :
    deformationMap I J f hf (Iff.BundleCycles.reesToDeformation I p) =
      Iff.BundleCycles.reesToDeformation J (reesMap I J f hf p) := by
  apply Subtype.ext
  ext n
  rw [deformationMap_coeff]
  by_cases hn : n ≤ 0
  · have he : n = -((-n).toNat : ℤ) := by omega
    rw [he, Iff.BundleCycles.reesToDeformation_coeff, Iff.BundleCycles.reesToDeformation_coeff, reesMap_coeff]
  · rw [Iff.BundleCycles.reesToDeformation_coeff_pos I p n (by omega), map_zero,
      Iff.BundleCycles.reesToDeformation_coeff_pos J _ n (by omega)]

theorem reesMap_normalConeIdeal (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) : Normal.Cone.BundleCycles.normalConeIdeal I ≤ (Normal.Cone.BundleCycles.normalConeIdeal J).comap (reesMap I J f hf) := by
  intro p hp
  rw [Ideal.mem_comap, ReesCoefficients.BundleCycles.mem_normalConeIdeal_iff]
  intro n
  rw [reesMap_coeff]
  exact map_idealPower_mem I J f hf _ ((ReesCoefficients.BundleCycles.mem_normalConeIdeal_iff I p).mp hp n)

/-- The induced homomorphism of actual normal-cone rings. -/
def normalConeMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) :
    Normal.Cone.BundleCycles.NormalConeRing I →+* Normal.Cone.BundleCycles.NormalConeRing J :=
  Ideal.quotientMap (Normal.Cone.BundleCycles.normalConeIdeal J) (reesMap I J f hf)
    (reesMap_normalConeIdeal I J f hf)

theorem deformationMap_specialIdeal (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    Iff.BundleCycles.deformationSpecialIdeal I ≤ (Iff.BundleCycles.deformationSpecialIdeal J).comap (deformationMap I J f hf) := by
  intro p hp
  rw [Ideal.mem_comap, Iff.BundleCycles.mem_deformationSpecialIdeal_iff]
  intro n
  rw [deformationMap_coeff]
  exact map_idealPower_mem I J f hf _ ((Iff.BundleCycles.mem_deformationSpecialIdeal_iff I p).mp hp n)

/-- The induced homomorphism of closed deformation fibers. -/
def deformationSpecialMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) : SpecialFiber.BundleCycles.DeformationSpecialRing I →+* SpecialFiber.BundleCycles.DeformationSpecialRing J :=
  Ideal.quotientMap (Iff.BundleCycles.deformationSpecialIdeal J) (deformationMap I J f hf)
    (deformationMap_specialIdeal I J f hf)

/-- Naturality of the canonical identification of the special fiber. -/
theorem normalConeSpecialFiberEquiv_natural (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (x : Normal.Cone.BundleCycles.NormalConeRing I) :
    deformationSpecialMap I J f hf (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I x) =
      SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv J (normalConeMap I J f hf x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv_mk]
  change Ideal.Quotient.mk (Iff.BundleCycles.deformationSpecialIdeal J)
      (deformationMap I J f hf (Iff.BundleCycles.reesToDeformation I p)) =
    SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv J
      (Ideal.Quotient.mk (Normal.Cone.BundleCycles.normalConeIdeal J) (reesMap I J f hf p))
  rw [SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv_mk, deformationMap_reesToDeformation]

@[simp]
theorem deformationMap_algebraMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (r : R) :
    deformationMap I J f hf (algebraMap R (Iff.BundleCycles.deformationAlgebra I) r) =
      algebraMap S (Iff.BundleCycles.deformationAlgebra J) (f r) := by
  apply Subtype.ext
  exact AddMonoidAlgebra.mapRingHom_single f 0 r

@[simp]
theorem deformationMap_monomial (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (n : ℤ) (r : R) (hr : r ∈ I ^ (-n).toNat) :
    deformationMap I J f hf (Iff.BundleCycles.deformationMonomial I n r hr) =
      Iff.BundleCycles.deformationMonomial J n (f r) (map_idealPower_mem I J f hf _ hr) := by
  apply Subtype.ext
  exact AddMonoidAlgebra.mapRingHom_single f n r

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps.BundleCycles
