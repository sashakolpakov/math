import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCechGluing

/-! # Affine Local Lifts -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineLocalLifts.Construction

noncomputable section

/-! Correction and gluing of local lifts when the kernel is quasicoherent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v

variable (R : CommRingCat.{u})
    (F E G : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of (PrimeSpectrum R)))
    (a : F ⟶ E) (b : E ⟶ G)
    (hF : ∀ r : R, IsLocalizedModule (Submonoid.powers r)
      (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom)
    (ha : ∀ r : R, Function.Injective (a.hom.app (op (PrimeSpectrum.basicOpen r))))
    (hab : ∀ r : R, Function.Exact (a.hom.app (op (PrimeSpectrum.basicOpen r)))
      (b.hom.app (op (PrimeSpectrum.basicOpen r))))
    {ι : Type v} [Fintype ι] [DecidableEq ι] (f : ι → R)

include hF ha hab in
theorem affineCech_correct_local_lifts (hf : Ideal.span (Set.range f) = ⊤)
    (s : G.obj.obj (op ⊤)) (x : AffineCech.Construction.affineCechC0 R E f)
    (hx : AffineCechGluing.Construction.affineCechMap0 R E f b x = AffineCechGluing.Construction.affineCechUnit R G f s) :
    ∃ y : AffineCech.Construction.affineCechC0 R E f,
      AffineCech.Construction.affineCechD0 R E f y = 0 ∧ AffineCechGluing.Construction.affineCechMap0 R E f b y = AffineCechGluing.Construction.affineCechUnit R G f s := by
  have hd : AffineCechGluing.Construction.affineCechMap1 R E f b (AffineCech.Construction.affineCechD0 R E f x) = 0 := by
    rw [← AffineCechGluing.Construction.affineCechMap0_d, hx, AffineCechGluing.Construction.affineCechUnit_d]
  have hker (i j : ι) :
      b.hom.app (op (PrimeSpectrum.basicOpen (f i * f j)))
        (AffineCech.Construction.affineCechD0 R E f x i j) = 0 := congrFun (congrFun hd i) j
  choose c hc using fun i j ↦ (hab (f i * f j) (AffineCech.Construction.affineCechD0 R E f x i j)).mp (hker i j)
  have hc' : AffineCechGluing.Construction.affineCechMap1 R F f a c = AffineCech.Construction.affineCechD0 R E f x := by
    funext i j
    exact hc i j
  have hdc : AffineCech.Construction.affineCechD1 R F f c = 0 := by
    apply AffineCechGluing.Construction.affineCechMap2_injective R F f a ha
    rw [map_zero, ← AffineCechGluing.Construction.affineCechMap1_d, hc']
    exact LinearMap.congr_fun (AffineCechGluing.Construction.affineCechD1_comp_D0_unconditional R E f) x
  obtain ⟨t, ht⟩ := (AffineCech.Construction.affineCech_exact_degreeOne R F hF f hf c).mp hdc
  refine ⟨x - AffineCechGluing.Construction.affineCechMap0 R F f a t, ?_, ?_⟩
  · rw [map_sub, AffineCechGluing.Construction.affineCechMap0_d, ht, hc', sub_self]
  · rw [map_sub, hx]
    have hz : AffineCechGluing.Construction.affineCechMap0 R E f b (AffineCechGluing.Construction.affineCechMap0 R F f a t) = 0 := by
      funext i
      exact (hab (f i) (a.hom.app (op (PrimeSpectrum.basicOpen (f i))) (t i))).mpr ⟨t i, rfl⟩
    rw [hz, sub_zero]

include hF ha hab in
theorem affine_global_lift_of_principal_local_lifts (hf : Ideal.span (Set.range f) = ⊤)
    (s : G.obj.obj (op ⊤)) (x : AffineCech.Construction.affineCechC0 R E f)
    (hx : AffineCechGluing.Construction.affineCechMap0 R E f b x = AffineCechGluing.Construction.affineCechUnit R G f s) :
    ∃ t : E.obj.obj (op ⊤), b.hom.app (op ⊤) t = s := by
  obtain ⟨y, hy, hby⟩ := affineCech_correct_local_lifts R F E G a b hF ha hab f hf s x hx
  obtain ⟨t, ht, _⟩ := AffineCechGluing.Construction.affineCech_sections_glue R E f hf y hy
  refine ⟨t, ?_⟩
  apply G.eq_of_locally_eq' (fun i ↦ PrimeSpectrum.basicOpen (f i)) ⊤
    (fun _ ↦ homOfLE le_top) (by rw [(PrimeSpectrum.iSup_basicOpen_eq_top_iff).mpr hf])
  intro i
  change G.obj.map (PrimeSpectrum.basicOpen (f i)).leTop.op (b.hom.app (op ⊤) t) = _
  rw [← NatTrans.naturality_apply, ht i]
  exact congrFun hby i

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineLocalLifts.Construction
