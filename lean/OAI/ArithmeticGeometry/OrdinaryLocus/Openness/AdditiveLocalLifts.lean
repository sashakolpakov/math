import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.QuasicoherentAdditiveCech

/-! # Additive Local Lifts -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveLocalLifts.Construction

noncomputable section

/-! Correction and gluing of local lifts when the kernel is acyclic in degree one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v

variable (R : CommRingCat.{u})
    (F E G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (PrimeSpectrum R)))
    (a : F ⟶ E) (b : E ⟶ G)
    (ha : ∀ r : R, Function.Injective (a.hom.app (op (PrimeSpectrum.basicOpen r))))
    (hab : ∀ r : R, Function.Exact (a.hom.app (op (PrimeSpectrum.basicOpen r)))
      (b.hom.app (op (PrimeSpectrum.basicOpen r))))
    {ι : Type v} (f : ι → R)
    (hF : Function.Exact (AdditiveCech.Construction.additiveAffineD0 R F f) (AdditiveCech.Construction.additiveAffineD1 R F f))

include hF ha hab in
theorem additiveAffine_correct_local_lifts (_hf : Ideal.span (Set.range f) = ⊤)
    (s : G.obj.obj (op ⊤)) (x : AdditiveCech.Construction.additiveAffineC0 R E f)
    (hx : AdditiveCech.Construction.additiveAffineMap0 R E f b x = AdditiveCech.Construction.additiveAffineUnit R G f s) :
    ∃ y : AdditiveCech.Construction.additiveAffineC0 R E f,
      AdditiveCech.Construction.additiveAffineD0 R E f y = 0 ∧ AdditiveCech.Construction.additiveAffineMap0 R E f b y = AdditiveCech.Construction.additiveAffineUnit R G f s := by
  have hd : AdditiveCech.Construction.additiveAffineMap1 R E f b (AdditiveCech.Construction.additiveAffineD0 R E f x) = 0 := by
    rw [← AdditiveCech.Construction.additiveAffineMap0_d, hx, AdditiveCech.Construction.additiveAffineUnit_d]
  have hker (i j : ι) :
      b.hom.app (op (PrimeSpectrum.basicOpen (f i * f j)))
        (AdditiveCech.Construction.additiveAffineD0 R E f x i j) = 0 := congrFun (congrFun hd i) j
  choose c hc using fun i j ↦ (hab (f i * f j) (AdditiveCech.Construction.additiveAffineD0 R E f x i j)).mp (hker i j)
  have hc' : AdditiveCech.Construction.additiveAffineMap1 R F f a c = AdditiveCech.Construction.additiveAffineD0 R E f x := by
    funext i j
    exact hc i j
  have hdc : AdditiveCech.Construction.additiveAffineD1 R F f c = 0 := by
    apply AdditiveCech.Construction.additiveAffineMap2_injective R F f a ha
    rw [map_zero, ← AdditiveCech.Construction.additiveAffineMap1_d, hc']
    exact DFunLike.congr_fun (AdditiveCech.Construction.additiveAffineD1_comp_D0 R E f) x
  obtain ⟨t, ht⟩ := (hF c).mp hdc
  refine ⟨x - AdditiveCech.Construction.additiveAffineMap0 R F f a t, ?_, ?_⟩
  · rw [map_sub, AdditiveCech.Construction.additiveAffineMap0_d, ht, hc', sub_self]
  · rw [map_sub, hx]
    have hz : AdditiveCech.Construction.additiveAffineMap0 R E f b (AdditiveCech.Construction.additiveAffineMap0 R F f a t) = 0 := by
      funext i
      exact (hab (f i) (a.hom.app (op (PrimeSpectrum.basicOpen (f i))) (t i))).mpr ⟨t i, rfl⟩
    rw [hz, sub_zero]

include hF ha hab in
theorem additiveAffine_global_lift (hf : Ideal.span (Set.range f) = ⊤)
    (s : G.obj.obj (op ⊤)) (x : AdditiveCech.Construction.additiveAffineC0 R E f)
    (hx : AdditiveCech.Construction.additiveAffineMap0 R E f b x = AdditiveCech.Construction.additiveAffineUnit R G f s) :
    ∃ t : E.obj.obj (op ⊤), b.hom.app (op ⊤) t = s := by
  obtain ⟨y, hy, hby⟩ := additiveAffine_correct_local_lifts R F E G a b ha hab f hF hf s x hx
  obtain ⟨t, ht, _⟩ := AdditiveCech.Construction.additiveAffine_sections_glue R E f hf y hy
  refine ⟨t, ?_⟩
  apply G.eq_of_locally_eq' (fun i ↦ PrimeSpectrum.basicOpen (f i)) ⊤
    (fun _ ↦ homOfLE le_top) (by rw [(PrimeSpectrum.iSup_basicOpen_eq_top_iff).mpr hf])
  intro i
  change G.obj.map (PrimeSpectrum.basicOpen (f i)).leTop.op (b.hom.app (op ⊤) t) = _
  rw [← NatTrans.naturality_apply, ht i]
  exact congrFun hby i

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveLocalLifts.Construction
