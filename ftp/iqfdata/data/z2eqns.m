K<t>:=NumberField(x^2+2);
R:=MaximalOrder(K);

function tzi(ai,n)
     E:=EllipticCurve(ai);//ai;
     if BaseRing(E) eq Q then E:=BaseChange(E,K); end if;
     return <K!n, MyConductor(E) eq ideal<R|n>>;
     end function;

tzi([ t  ,1 - t  ,1  ,-1  ,0  ]                                , 1 - 2*t  );
tzi([0  ,0  ,0  ,1  ,0  ]                                      , 4*t  );
tzi([0  ,0  ,0  ,-1  ,0  ]                                     , 4*t  );
tzi([ t  ,-1  , t  ,-1  ,0  ]                                  , 4*t  );
tzi([ t  ,-1  ,0  ,-2  ,3  ]                                   , 4*t  );
tzi([ t  ,-1 + t  ,1  , -t  ,0  ]                              , 7 + t  );
tzi([ t  ,-1 + t  ,1 + t  ,2 -2*t  ,0  ]                        , 7 + t  );
tzi([1 + t  ,0  ,1  ,-1 - t  ,0  ]                             , 2 + 5*t  );
tzi([1  ,1 - t  ,0  ,-1 - t  ,-1  ]                            , 2 + 5*t  );
tzi([1  ,1 - t  ,0  ,4 -11*t  ,-26  ]                           , 2 + 5*t  );
tzi([1  ,1 - t  ,0  ,69 -51*t  ,339 +62*t  ]                     , 2 + 5*t  );
tzi([ t  ,1  , t  ,0  ,0  ]                                    , 6*t  );
tzi([ t  ,1  , t  ,-15  ,-27  ]                                , 6*t  );
tzi([ t  ,1  , t  ,-5  ,5  ]                                   , 6*t  );
tzi([0  ,-1  ,0  ,1  ,0  ]                                     , 6*t  );
tzi([ t  ,1  , t  ,-95  ,347  ]                                , 6*t  );
tzi([ t  ,1  , t  ,5  ,23  ]                                   , 6*t  );
tzi([ t  ,1  , t  ,85 +70*t  ,559 -98*t  ]                       , 6*t  );
tzi([ t  ,1  , t  ,85 -70*t  ,559 +98*t  ]                       , 6*t  );
tzi([1  ,0  ,1  ,-1  ,0  ]                                     , 7*t  );
tzi([1  ,0  ,1  ,-11  ,12  ]                                   , 7*t  );
tzi([1  ,0  ,1  ,4  ,-6  ]                                     , 7*t  );
tzi([1  ,0  ,1  ,-36  ,-70  ]                                  , 7*t  );
tzi([1  ,0  ,1  ,-171  ,-874  ]                                , 7*t  );
tzi([1  ,0  ,1  ,-2731  ,-55146  ]                             , 7*t  );
tzi([1 + t  ,1 - t  ,1 + t  ,-2*t  , -t  ]                      , 9 + 3*t  );
tzi([1 + t  ,1 - t  ,1 + t  ,-5 -2*t  ,4 + t  ]                 , 9 + 3*t  );
tzi([1 + t  ,1 - t  ,1 + t  ,-90 -12*t  ,302 +71*t  ]            , 9 + 3*t  );
tzi([1 + t  ,1 - t  ,1 + t  ,8*t  ,22 +19*t  ]                   , 9 + 3*t  );
tzi([1 + t  ,1 - t  ,1 + t  ,-15 +173*t  ,1006 +859*t  ]         , 9 + 3*t  );
tzi([1 + t  ,1 - t  ,1 + t  ,95 +3*t  ,-30 +251*t  ]             , 9 + 3*t  );
tzi([0  ,1  ,0  ,-1  ,0  ]                                     , 10  );
tzi([ t  ,0  , t  ,2  ,0  ]                                    , 10  );
tzi([0  ,1  ,0  ,-41  ,-116  ]                                 , 10  );
tzi([ t  ,0  , t  ,-8  ,18  ]                                  , 10  );
tzi([ t  ,1 - t  , t  ,4 -3*t  ,4 -2*t  ]                        , 6 + 6*t  );
tzi([ t  ,1 - t  , t  ,49 -48*t  ,265 +7*t  ]                    , 6 + 6*t  );
tzi([0  ,-1 - t  ,0  ,9  ,-2 +5*t  ]                            , 6 + 6*t  );
tzi([ t  ,1 - t  , t  ,-21 +2*t  ,37 +13*t  ]                    , 6 + 6*t  );
tzi([ t  ,1 - t  ,0  ,-1 -4*t  ,-7 + t  ]                       , 6 + 6*t  );
tzi([ t  ,1 - t  ,0  ,14 +11*t  ,-19 +16*t  ]                    , 6 + 6*t  );
tzi([0  ,-1 - t  ,0  ,-7 -4*t  ,4 +11*t  ]                       , 6 + 6*t  );
tzi([ t  ,1 - t  ,0  ,4 -59*t  ,-261 +122*t  ]                   , 6 + 6*t  );
tzi([1  , -t  , t  , -t  ,0  ]                                 , 4 + 7*t  );
tzi([1  , -t  , t  ,10 - t  ,2 +6*t  ]                          , 4 + 7*t  );
tzi([1  , -t  , t  ,170 -6*t  ,68 +549*t  ]                      , 4 + 7*t  );
tzi([1  , -t  , t  ,10 +4*t  ,24 +7*t  ]                         , 4 + 7*t  );
tzi([0  ,-1  ,1  ,0  ,0  ]                                     , 11  );
tzi([0  ,-1  ,1  ,-10  ,-20  ]                                 , 11  );
tzi([0  ,-1  ,1  ,-7820  ,-263580  ]                           , 11  );
tzi([ t  ,1  ,1  ,3 -3*t  ,-3 - t  ]                            , 7 - 6*t  );
tzi([ t  ,0  , t  ,0  ,1  ]                                    , 12  );
tzi([ t  ,0  , t  ,-15  ,28  ]                                 , 12  );
tzi([ t  ,0  , t  ,-5  ,-4  ]                                  , 12  );
tzi([0  ,1  ,0  ,1  ,0  ]                                      , 12  );
tzi([ t  ,0  , t  ,-95  ,-346  ]                               , 12  );
tzi([ t  ,0  , t  ,5  ,-22  ]                                  , 12  );
tzi([ t  ,0  , t  ,85 -70*t  ,-558 -98*t  ]                      , 12  );
tzi([ t  ,0  , t  ,85 +70*t  ,-558 +98*t  ]                      , 12  );
tzi([ t  ,1 - t  , t  ,2  ,1 - t  ]                            , 6 + 8*t  );
tzi([0  ,-1 - t  ,0  ,1 +2*t  ,2 - t  ]                         , 6 + 8*t  );
tzi([1 + t  ,-1 + t  ,1  ,-2 -2*t  ,1  ]                        , 4 + 9*t  );
tzi([1 + t  ,-1 + t  ,1  ,8 -17*t  ,55 +6*t  ]                   , 4 + 9*t  );
tzi([1  , t  ,1  ,-1  ,0  ]                                    , 12 + 5*t  );
tzi([1  ,1 - t  , t  ,2  ,2 -2*t  ]                             , 10 + 7*t  );
tzi([1  ,1 - t  , t  ,42 +10*t  ,86 -80*t  ]                     , 10 + 7*t  );
tzi([1 + t  ,0  ,1 + t  ,1 + t  ,2 + t  ]                      , 10 + 7*t  );
tzi([1 + t  ,0  ,1 + t  ,-19 -4*t  ,38 + t  ]                   , 10 + 7*t  );
tzi([0  ,0  ,0  ,-2  ,1  ]                                     , 10*t  );
tzi([ t  ,-1  , t  ,0  ,2  ]                                   , 10*t  );
tzi([ t  ,-1  , t  ,-25  ,67  ]                                , 10*t  );
tzi([ t  ,-1  , t  ,5  ,3  ]                                   , 10*t  );
tzi([ t  , t  ,1 + t  , t  ,0  ]                               , 11 + 7*t  );
tzi([ t  , t  ,1 + t  , -t  , -t  ]                            , 11 + 7*t  );
tzi([1  ,1  ,1  ,0  ,0  ]                                      , 15  );
tzi([1  ,1  ,1  ,-5  ,2  ]                                     , 15  );
tzi([1  ,1  ,1  ,-80  ,242  ]                                  , 15  );
tzi([1  ,1  ,1  ,-10  ,-10  ]                                  , 15  );
tzi([1  ,1  ,1  ,-135  ,-660  ]                                , 15  );
tzi([1  ,1  ,1  ,35  ,-28  ]                                   , 15  );
tzi([1  ,1  ,1  ,-2160  ,-39540  ]                             , 15  );
tzi([1  ,1  ,1  ,-110  ,-880  ]                                , 15  );
tzi([ t  ,-1  ,1 + t  ,2 -3*t  ,5 - t  ]                        , 5 + 10*t  );
tzi([ t  ,-1  ,1  ,8 +2*t  ,-9 +4*t  ]                           , 5 + 10*t  );
tzi([1 + t  , t  ,1  ,13 +9*t  ,40 +10*t  ]                      , 12 + 7*t  );
tzi([1  ,1  ,0  ,-194 -35*t  ,938 +268*t  ]                      , 12 + 7*t  );
tzi([1  ,1  , t  ,-41 +7*t  ,-121 +29*t  ]                       , 12 + 7*t  );
tzi([1 + t  , t  ,1  ,-13 -41*t  ,122 -109*t  ]                  , 12 + 7*t  );
tzi([1 + t  , -t  ,1 + t  ,-3*t  ,0  ]                          , 2 + 11*t  );
tzi([1  ,-1 + t  ,1  ,-1 + t  ,-2 - t  ]                       , 7 + 10*t  );
tzi([0  , t  ,0  ,1  , t  ]                                    , 16  );
tzi([0  , -t  ,0  ,1  , -t  ]                                  , 16  );
tzi([0  ,-1  ,0  ,-2  ,2  ]                                    , 16  );
tzi([0  ,-1  ,0  ,1  ,-1  ]                                    , 16  );
tzi([0  ,1  ,0  ,-2  ,-2  ]                                    , 16  );
tzi([0  ,1  ,0  ,1  ,1  ]                                      , 16  );
tzi([1 + t  , t  ,0  , -t  ,0  ]                               , 16 + t  );
tzi([1 + t  , t  ,0  ,4*t  ,-12 - t  ]                          , 16 + t  );
tzi([ t  ,1  , t  ,-1 -2*t  ,-1 -2*t  ]                          , 16 + 2*t  );
tzi([ t  ,1  , t  ,-1 +8*t  ,-1 -12*t  ]                         , 16 + 2*t  );
tzi([ t  ,0  ,1 + t  ,-2*t  ,-1 -3*t  ]                          , 5 + 11*t  );
tzi([ t  ,0  ,1 + t  ,8 -4*t  ,7 +4*t  ]                         , 5 + 11*t  );
tzi([ t  ,0  ,1 + t  ,-170 -157*t  ,-332 -1222*t  ]              , 5 + 11*t  );
tzi([ t  ,0  ,1 + t  ,-42 -39*t  ,48 +165*t  ]                   , 5 + 11*t  );
tzi([0  ,1  ,0  ,-2  ,0  ]                                     , 12*t  );
tzi([ t  ,0  , t  ,-7  ,-7  ]                                  , 12*t  );
tzi([0  ,1  ,0  ,-4  ,2  ]                                     , 12*t  );
tzi([ t  ,0  ,0  ,2  ,-1  ]                                    , 12*t  );
tzi([ t  ,0  ,0  ,22 +5*t  ,-23 +26*t  ]                         , 12*t  );
tzi([ t  ,0  ,0  ,22 -5*t  ,-23 -26*t  ]                         , 12*t  );
tzi([0  ,-1  ,0  ,-2  ,0  ]                                    , 12*t  );
tzi([ t  ,1  , t  ,-7  ,8  ]                                   , 12*t  );
tzi([0  ,-1  ,0  ,-4  ,-2  ]                                   , 12*t  );
tzi([ t  ,1  ,0  ,2  ,1  ]                                     , 12*t  );
tzi([ t  ,1  ,0  ,22 +5*t  ,23 -26*t  ]                          , 12*t  );
tzi([ t  ,1  ,0  ,22 -5*t  ,23 +26*t  ]                          , 12*t  );
tzi([0  , t  ,0  ,1  ,3*t  ]                                    , 12*t  );
tzi([0  , t  ,0  ,11  ,-7*t  ]                                  , 12*t  );
tzi([ t  ,-1 + t  ,0  ,-2 +4*t  ,-5 -8*t  ]                      , 12*t  );
tzi([ t  ,-1 + t  , t  ,-1 -6*t  ,8 -3*t  ]                      , 12*t  );
tzi([ t  ,-1 + t  ,0  ,-32 +79*t  ,-215 -374*t  ]                , 12*t  );
tzi([ t  ,-1 + t  ,0  ,-12 +9*t  ,-15 +6*t  ]                    , 12*t  );
tzi([ t  ,-1 + t  , t  ,-31 -81*t  ,248 -294*t  ]                , 12*t  );
tzi([ t  ,-1 + t  , t  ,-11 -11*t  ,28 +16*t  ]                  , 12*t  );
tzi([0  , -t  ,0  ,1  ,-3*t  ]                                  , 12*t  );
tzi([0  , -t  ,0  ,11  ,7*t  ]                                  , 12*t  );
tzi([ t  ,-1 - t  , t  ,-1 +6*t  ,8 +3*t  ]                      , 12*t  );
tzi([ t  ,-1 - t  ,0  ,-2 -4*t  ,-5 +8*t  ]                      , 12*t  );
tzi([ t  ,-1 - t  , t  ,-31 +81*t  ,248 +294*t  ]                , 12*t  );
tzi([ t  ,-1 - t  , t  ,-11 +11*t  ,28 -16*t  ]                  , 12*t  );
tzi([ t  ,-1 - t  ,0  ,-32 -79*t  ,-215 +374*t  ]                , 12*t  );
tzi([ t  ,-1 - t  ,0  ,-12 -9*t  ,-15 -6*t  ]                    , 12*t  );
tzi([1  ,-1  ,1  ,-1  ,0  ]                                    , 17  );
tzi([1  ,-1  ,1  ,-6  ,-4  ]                                   , 17  );
tzi([1  ,-1  ,1  ,-91  ,-310  ]                                , 17  );
tzi([1  ,-1  ,1  ,-1  ,-14  ]                                  , 17  );
tzi([ t  ,1 - t  ,1 + t  ,-1 - t  ,1  ]                        , 15 + 6*t  );
tzi([ t  ,1 - t  ,1 + t  ,1 + t  , -t  ]                       , 15 + 6*t  );
tzi([ t  ,1 - t  ,1 + t  ,-1 -46*t  ,104 -109*t  ]               , 15 + 6*t  );
tzi([ t  ,1 - t  ,1 + t  ,1 -14*t  ,-17 +7*t  ]                  , 15 + 6*t  );
tzi([0  ,-1 + t  ,1  ,1 - t  , t  ]                            , 13 + 8*t  );
tzi([0  ,-1 + t  ,1  ,11 -11*t  ,-27 +3*t  ]                     , 13 + 8*t  );
tzi([0  ,-1 + t  ,1  ,-9 +39*t  ,-210 -39*t  ]                   , 13 + 8*t  );
tzi([0  ,1 - t  ,1  ,2 -2*t  ,1  ]                              , 13 + 8*t  );
tzi([ t  ,1 - t  ,1 + t  ,-3*t  ,1 -2*t  ]                       , 3 + 12*t  );
tzi([ t  ,1 - t  ,1  ,-6 -2*t  ,-7  ]                           , 3 + 12*t  );
