{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Karamaan.Opaleye.Default where

import Karamaan.Opaleye.Wire (Wire(Wire), unWire)
import Karamaan.Opaleye.Colspec (Colspec'(Colspec'), Writer(Writer),
                                 PackMap(PackMap))
import Karamaan.Opaleye.ProductProfunctor

class Default p a b where
  -- Would rather call it "default", but that's a keyword
  def :: p a b

instance Default Colspec' (Wire a) (Wire a) where
  def = Colspec' (Writer (return . unWire)) (PackMap (\f -> Wire . f . unWire))

instance (ProductProfunctor p, Default p a1 b1, Default p a2 b2)
         => Default p (a1, a2) (b1, b2) where
  def = p2 (def, def)

instance (ProductProfunctor p, Default p a1 b1, Default p a2 b2,
          Default p a3 b3)
         => Default p (a1, a2, a3)
                      (b1, b2, b3) where
  def = p3 (def, def, def)

instance (ProductProfunctor p, Default p a1 b1, Default p a2 b2,
          Default p a3 b3, Default p a4 b4, Default p a5 b5)
         => Default p (a1, a2, a3, a4, a5)
                      (b1, b2, b3, b4, b5) where
  def = p5 (def, def, def, def, def)

instance (ProductProfunctor p, Default p a1 b1, Default p a2 b2,
          Default p a3 b3, Default p a4 b4, Default p a5 b5,
          Default p a6 b6, Default p a7 b7)
         => Default p (a1, a2, a3, a4, a5, a6, a7)
                      (b1, b2, b3, b4, b5, b6, b7) where
  def = p7 (def, def, def, def, def, def, def)

instance (ProductProfunctor p, Default p a1 b1, Default p a2 b2,
          Default p a3 b3, Default p a4 b4, Default p a5 b5,
          Default p a6 b6, Default p a7 b7, Default p a8 b8)
         => Default p (a1, a2, a3, a4, a5, a6, a7, a8)
                      (b1, b2, b3, b4, b5, b6, b7, b8) where
  def = p8 (def, def, def, def, def, def, def, def)
