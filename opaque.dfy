/*
 * Var naming convention:
 * a: ActorAddr
 * i: Addr
 * c: Config
 * st: State
 */
abstract module Opaque{
    ////CONFIG////
    type Config
    type Actor
    type Frame
    //old app constructor app(is, b) left in for backwards compatibility 
    // with earlier versions of the paper
    datatype Msg = orca(i: Addr, z: int) | app(is: set<Addr>, b: BId) | app'(f: Frame)| ERR
    function Heap(c: Config, i: Addr, fid: FId) : Addr
    function allocated_addresses(c: Config) : set<Addr>

    ////IDs////
    type FId
    type BId
    type ClassId
    type VarId

    ////ADDRESSES////
    datatype Addr = OA(ObjectAddr) | AA(ActorAddr) | Null
    type ObjectAddr
    type ActorAddr

    ////PATHS////
    datatype Capability = WRITE | READ | TAG | ERR
    type DP
    type SP

    datatype Optional<T> = Some(o: T) | None

    ////ACTORS////
    //lemma all valid actor addresses are in the domain of Actors
    function Actors(c: Config, a: ActorAddr) : Actor



    ////REFERENCE COUNTS////
    function RC(c: Config, i: Addr, a: ActorAddr) : nat
    function OMC(c: Config, i: Addr) : int
    function LRC(c: Config, i: Addr) : int
    function FRC(c: Config, i: Addr) : int
    function AMC(c: Config, i: Addr) : int
    
    lemma LRC_is_owner_RC(c: Config, i: Addr, a: ActorAddr)
        requires Owner(c, i, a)
        ensures LRC(c, i) == RC(c, i, a)
    
    lemma FRC_is_not_owner_RC(c: Config, i: Addr, actors: set<ActorAddr>) 
        requires forall a ::    
                    a in actors <==>
                    !Owner(c, i, a) 
        ensures FRC(c, i) == sum_over_set_RC(c, actors)

    function sum_over_set_RC(c: Config, actors: set<ActorAddr>) : nat
    /////////////////////////


    /////DATA RACE FREEDOM/////
    predicate DRF(c: Config) {
        forall a, a': ActorAddr, p, p': DP, i: Addr, k: Capability ::
            a != a' &&
            A(c, a, p, i, WRITE) &&
            A(c, a', p', i, k) ==>
            k == TAG
    }
    /////////////////////////


    //////ACCESSIBILITY/REACHABILITY////// 
    predicate A(c: Config, a: ActorAddr, dp: DP, i: Addr, k: Capability)

    predicate accessible_via_lp(c: Config, i: Addr, a: ActorAddr) {
        exists lp,k ::
            A(c, a, lp, i, k)
    }

    predicate is_a_message_path(c: Config, mp: DP)

    predicate live(c: Config, a: ActorAddr, i: Addr) {
        exists k, dp ::
            A(c, a, dp, i, k)
    }

    predicate msg_live(c: Config, a: ActorAddr, i: Addr, n: nat) {
        (exists k, mp ::
            A(c, a, mp, i, k) &&
            is_a_message_path(c, mp) &&
            message_path_from_n(c, mp, n)) ||
        (queue_at_n_orca(c, a, n) &&
        queue_at_n_orca_i(c, a, n) == i)
    }

    predicate message_path_from_n(c: Config, mp: DP, n: nat)

    predicate Reachable(c: Config, iota: Addr, a: ActorAddr, f: Frame)

    function all_reachable(c: Config, a: ActorAddr, f: Frame) : set<Addr>
    /////////////////////////


    //////////////////////////////INVARIANTS///////////////////////////////

    predicate INV_1() {
        forall c ::
            DRF(c)
    }

    predicate INV_2(c: Config) {
        forall i, dp, mp, k, a, a_own ::
            (A(c, a, dp, i, k) &&
            !Owner(c, i, a)) ||
            (A(c, a_own, mp, i, k) &&
            Owner(c, i, a_own) &&
            is_a_message_path(c, mp)) ==>
            LRC(c, i) > 0
    }

    predicate INV_3(c: Config) {
        forall i, dp, k, a ::
            A(c, a, dp, i, k) &&
            !Owner(c, i, a) ==>
            RC(c, i, a) > 0
    }

    predicate INV_4(c: Config) {
        forall i ::
            LRC(c, i) + OMC(c, i) == FRC(c, i) + AMC(c, i)
    }

    predicate INV_5(c: Config) 
    //RC returns a nat. Therefore, INV_5 holds implicitly

    predicate INV_6(c: Config) {
        forall i, a :: Owner(c, i, a) ==>

            (forall n: nat ::
                n <= queue_length(c, a) ==>
                LRC_plus_queue_effect(c, a, i, n) >= 0) &&

            (forall a' ::
                a != a' &&
                live(c, a', i) ==>
                forall j: nat ::
                    j <= queue_length(c, a) ==>
                    LRC_plus_queue_effect(c, a, i, j) > 0) &&

            (forall n: nat ::
                n < queue_length(c, a) &&
                msg_live(c, a, i, n) ==>
                forall j: nat ::
                    j <= n ==>
                    LRC_plus_queue_effect(c, a, i, j) > 0)
    }
    ///////////////////////////////////////////////////////////////////////////


    /////SYSTEM PROPERTIES/////
    predicate Ownership_Immutable(c: Config, c': Config)
    {
        forall i, a' :: 
            Owner(c, i, a') == Owner(c', i, a')
    }

    lemma Ownership_Unique(c: Config)
        ensures forall i, a, a' ::
            Owner(c, i, a) &&
            a != a' ==>
            !Owner(c, i, a')
    ///////////////////////////


    ///////////////PSEUDO CODE FOR RECEIVING MESSAGES (FIGURE 6)///////////////

    ////RcvApp////
    predicate RcvApp(c: Config, a: ActorAddr, c': Config)
        requires actor_state_idle(c, a)
        requires queue_at_n_app(c, a, 0)
    {
        actor_state_rcv(c', a) &&
        actor_ws(c', a) == set i |
            i in allocated_addresses(c) &&
            exists mp,k ::
            mp in paths_from_message_n(c, a, 0) &&
            A(c,a,mp,i,k)
    }

    ////RcvToExe////
    predicate RcvToExe(c: Config, a: ActorAddr, c': Config)
    {
        actor_state_rcv(c, a) &&
        queue_at_n_app(c, a, 0) &&
        actor_state_exe(c', a) &&
        actor_state_exe_f(c', a) == frame_from_app_message_n(c, a, 0) &&
        pop(c, a, c') &&
        Ownership_Immutable(c, c') &&

        (forall i :: 
            i in actor_ws(c, a) && 
            Owner(c, i, a) ==> 
            RC(c', i, a) == RC(c, i, a) - 1) &&

        (forall i :: 
            i in actor_ws(c, a) && 
            !Owner(c, i, a) ==> 
            RC(c', i, a) == RC(c, i, a) + 1) &&

        (forall i :: 
            i !in actor_ws(c, a) ==> 
            RC(c', i, a) == RC(c, i, a)) &&

        (forall i, a' :: 
            a' != a ==> 
            RC(c', i, a') == RC(c, i, a'))
    }


    lemma RcvToExe_Increases_A(c: Config, a: ActorAddr, c': Config)
        requires RcvToExe(c, a, c')
        ensures forall lp, i, k :: 
            A(c, a, lp, i, k) ==> 
            A(c', a, lp, i, k)

        ensures forall lp, i, k :: 
            A(c', a, lp, i, k) ==> 
            A(c, a, lp, i, k) || 
            i in actor_ws(c, a)

        ensures forall lp, i, k, a' :: 
            a' != a ==> 
            A(c', a', lp, i, k) == A(c, a', lp, i, k)


    lemma RcvToExe_Preserves_INV_3(c: Config, a': ActorAddr, c': Config)
        requires INV_3(c)
        requires RcvToExe(c, a', c')
        ensures INV_3(c')
    {
        RcvToExe_Increases_A(c, a', c');
        forall i, lp, k, a |
            A(c', a, lp, i, k) &&
            !Owner(c', i ,a)
            ensures RC(c', i, a) > 0
        {
            if a' == a && i in actor_ws(c, a) {
                assert RC(c, i, a) >= 0;
                assert RC(c', i, a) == RC(c, i, a) + 1;
            } else {
                assert RC(c', i, a) == RC(c, i, a);
                assert RC(c, i, a) > 0;
                assert RC(c', i, a) > 0;
            }
        }
    }

    ////AUXILIARY FOR RcvApp////
    predicate actor_state_idle(c: Config, a: ActorAddr)


    predicate actor_state_rcv(c: Config, a: ActorAddr)

    function paths_from_message_n(c: Config, a: ActorAddr, n: nat) : set<DP>
        requires n < queue_length(c, a)

    function actor_ws(c: Config, a: ActorAddr) : set<Addr>
        requires actor_state_rcv(c, a) || actor_state_snd(c, a)

    predicate Owner(c: Config, i: Addr, a: ActorAddr)

    predicate actor_state_exe(c: Config, a: ActorAddr)

    function frame_from_app_message_n(c: Config, a: ActorAddr, n: nat) : Frame
    ///////////////////////////

    ///////////////PSEUDO CODE FOR RECEIVING AN ORCA MESSAGE (FIGURE 7)///////////////

    ////rcvORCA////
    predicate rcvORCA(c: Config, a: ActorAddr, c': Config)
    {
        queue_at_n_orca(c, a, 0) &&
        var i := queue_at_n_orca_i(c, a, 0);
        var z := queue_at_n_orca_z(c, a, 0);

        Owner(c, i, a) &&
        queue_at_n_orca(c, a, 0) &&
        actor_state_idle(c, a) &&
        pop(c, a, c') &&
        RC(c', i, a) == RC(c, i, a) + z &&
        Ownership_Immutable(c, c') &&

        (forall a' :: 
            a' != a ==>
            unchanged_actor(c, a', c')) 
        //TODO: SD: what is state of actor a in c'? And what about the contents of actor's fields?
    }

    ////AUXILIARY FOR rcvORCA////
    lemma sum_over_orca_head_is_add_z(c: Config, i: Addr, a: ActorAddr)
        requires queue_at_n_orca(c, a, 0)
        ensures queue_effect(c, a, queue_at_n_orca_i(c, a, 0), 0, 1) == queue_at_n_orca_z(c, a, 0)
    
    function queue_effect(c: Config, a: ActorAddr, i: Addr, incl: nat, excl: nat) : int

    function LRC_plus_queue_effect(c: Config, a: ActorAddr, i: Addr, excl: nat) : int
    {
        LRC(c, i) + queue_effect(c, a, i, 0, excl)
    }

    lemma queue_effect_pop(c: Config, a: ActorAddr, c': Config, i: Addr, incl: nat, excl: nat)
        requires rcvORCA(c, a, c')
        requires incl>0
        requires excl>=incl
        ensures queue_effect(c', a, i, incl-1, excl-1) == queue_effect(c, a, i, incl, excl)

    lemma msg_live_pop(c: Config, a: ActorAddr, c': Config, i: Addr, n: nat)
        requires rcvORCA(c, a, c')
        requires msg_live(c', a, i, n)
        ensures msg_live(c, a, i, n+1)

    lemma LRC_plus_queue_effect_shift(c: Config, a: ActorAddr, c': Config, i: Addr, k: nat)
        requires rcvORCA(c, a, c')
        ensures LRC_plus_queue_effect(c, a, i, k+1) == LRC_plus_queue_effect(c', a, i, k)
        ensures forall a', i' ::
            a' != a &&
            Owner(c, i', a') ==>
            LRC_plus_queue_effect(c, a', i', k) == LRC_plus_queue_effect(c', a', i', k)

    lemma rcvORCA_accessibility_unaffected(c: Config, a: ActorAddr, i: Addr, c': Config)
        requires rcvORCA(c, a, c')
        requires queue_at_n_orca_i(c, a, 0) == i
        ensures forall a', i ::
            a' != a ==>
            (live(c, a', i) <==>
            live(c', a', i))
        ensures forall a, i' ::
            i != i' ==>
            (live(c, a, i') <==>
            live(c', a, i'))
    //////////////////////////////

    lemma rcvORCA_preserves_INV_6(c: Config, a_own: ActorAddr, c': Config)
        requires INV_6(c)
        requires INV_2(c)
        requires rcvORCA(c, a_own, c')
        ensures INV_6(c')
    {
        //INV_6.[b]
        forall a, i, j: nat |
                Owner(c', i, a) &&
                j <= queue_length(c', a)
                ensures LRC_plus_queue_effect(c', a, i, j) >= 0
        {
            if a == a_own {
                var i_0 := queue_at_n_orca_i(c, a, 0);
                if i == i_0 {
                    LRC_plus_queue_effect_shift(c, a, c', i, j);
                } else {
                    LRC_plus_queue_effect_shift(c, a, c', i, j);
                }
            } else {
                LRC_plus_queue_effect_shift(c, a_own, c', i, j);
                assert unchanged_actor(c, a, c');
            }
        }

        //INV_6.[c]
        forall a, a', i, j: nat |
            Owner(c', i, a) &&
            a != a' &&
            live(c', a', i) &&
            j <= queue_length(c', a)
            ensures LRC_plus_queue_effect(c', a, i, j) > 0
        {
            var i_0 := queue_at_n_orca_i(c, a_own, 0);
            if a == a_own {
                rcvORCA_accessibility_unaffected(c, a_own, i_0, c');
                LRC_plus_queue_effect_shift(c, a, c', i, j);
            } else {
                Ownership_Unique(c');
                rcvORCA_accessibility_unaffected(c, a_own, i_0, c');
                assert unchanged_actor(c, a, c');
                LRC_plus_queue_effect_shift(c, a_own, c', i, j);
            }
        }

        //INV_6.[a]
        forall a, i, j: nat, n: nat |
            Owner(c', i, a) &&
            n < queue_length(c', a) &&
            msg_live(c', a, i, n) &&
            j <= n
            ensures LRC_plus_queue_effect(c', a, i, j) > 0
        {
            var i_0 := queue_at_n_orca_i(c, a_own, 0);
            if a == a_own {
                LRC_plus_queue_effect_shift(c, a, c', i, j);
                msg_live_pop(c, a, c', i, n);
            } else {
                LRC_plus_queue_effect_shift(c, a_own, c', i, j);
                assert unchanged_actor(c, a, c');
            }


        }
    }

    ///////////////PSEUDO CODE FOR SENDING MESSAGES (FIGURE 8)///////////////

    ////ExeToSnd////
    predicate ExeToSnd(c: Config, a: ActorAddr, a': ActorAddr, c': Config, c'': Config, msg: Msg) 
        requires actor_state_exe(c, a)
        requires queue_at_n_app(c'', a', queue_length(c, a'))
        requires push(c, a', msg, c'') 
        requires msg.app?
        requires subset(frame_rng(msg_f(c, msg)), frame_rng(actor_state_exe_f(c, a)))
        requires disjoint(frame_dom(msg_f(c, msg)), frame_dom(actor_state_exe_f(c, a)))
        requires DRF(c'')
        
    {
        actor_state_snd(c', a) &&
        actor_state_snd_a'(c', a) == a' &&
        actor_state_snd_f'(c', a) == queue_at_n_app_f(c'', a', queue_length(c, a')) &&
        actor_state_snd_f(c', a) == actor_state_exe_f(c, a) &&
        actor_ws(c', a) == {} &&
        all_else_unmodified(c, a, c')
    }

    ////SndToExe////
    predicate SndToExe(c: Config, a: ActorAddr, a': ActorAddr, c': Config, c'': Config) 
    {
        actor_state_snd(c, a) &&
        actor_state_snd_a'(c, a) == a' &&

        all_else_unmodified(c, a, c') &&
        Ownership_Immutable(c, c') &&

        var f := actor_state_snd_f(c, a);
        var f' := actor_state_snd_f'(c, a);
        var ws := actor_ws(c, a);
        
        (forall i :: 
            i in ws && 
            Owner(c, i, a) ==> 
            RC(c', i, a) == RC(c, i, a) + 1 &&
            FRC(c', i) == FRC(c, i) &&
            OMC(c', i) == OMC(c, i) &&
            LRC(c', i) == LRC(c, i) + 1) &&

        (forall i :: 
            i in ws &&
            !Owner(c, i, a) &&
            RC(c, i, a) > 1 ==>
            RC(c', i, a) == RC(c, i, a) - 1 &&
            OMC(c', i) == OMC(c, i) &&
            LRC(c', i) == LRC(c, i) &&
            FRC(c', i) == FRC(c, i) - 1) &&
    
        (forall i :: 
            i in ws &&
            !Owner(c, i, a) &&
            RC(c, i, a) == 1 ==>
            RC(c', i, a) == RC(c, i, a) + 255 &&
            OMC(c', i) == OMC(c, i) + 256 &&
            LRC(c', i) == LRC(c, i) &&
            FRC(c', i) == FRC(c, i) + 255) &&

        actor_state_exe(c', a) &&
        actor_state_exe_f(c', a) == f &&

        (forall i ::
            i in ws ==>
            AMC(c', i) == AMC(c, i) + 1)
    }

    lemma SndToExe_preserves_INV_4(c: Config, a: ActorAddr, a': ActorAddr, c': Config, c'': Config, f': Frame)
        requires INV_4(c)
        requires SndToExe(c, a, a', c', c'')
        requires ws_WF(c, a, actor_state_snd_f(c, a), actor_state_snd_f'(c, a))
        ensures INV_4(c') 
    {
        forall i |
        true 
        ensures LRC(c', i) + OMC(c', i) == FRC(c', i) + AMC(c', i) 
        {   
            if (i in actor_ws(c, a)) {
                if(Owner(c, i, a)) {
                } else {
                    if RC(c, i, a) > 1 {
                    } else {
                        can_reach_ws(c);
                    }
                }
            } else {
            }
        }
    }

    lemma can_reach_ws(c: Config) 
        ensures forall a ::
                (actor_state_snd(c, a) ||
                actor_state_rcv(c, a)) ==>
                forall i ::
                    i in actor_ws(c, a) ==>
                    RC(c, i, a) >= 1
        
    /////////Auxiliary for ExeToSnd and SndToExe////////// 
    //these can be probably generalised into fewer methods - that is for later    

    predicate actor_state_snd(c: Config, a: ActorAddr)

    function actor_state_snd_msg(c: Config, a: ActorAddr) : Msg 
        requires actor_state_snd(c, a)

    function actor_state_snd_f'(c: Config, a: ActorAddr) : Frame
        requires actor_state_snd(c, a)

    function actor_state_snd_a'(c: Config, a: ActorAddr) : ActorAddr
        requires actor_state_snd(c, a)
     
    function msg_f(c: Config, msg: Msg) : Frame

    function actor_state_snd_f(c: Config, a: ActorAddr) : Frame 
        requires actor_state_snd(c, a)

    function actor_state_exe_f(c: Config, a: ActorAddr) : Frame 
        requires actor_state_exe(c, a)

    function queue_at_n_app_f(c: Config, a: ActorAddr, n: nat) : Frame
        requires queue_at_n_app(c, a, n)

    function frame_dom(f: Frame) : set<VarId>

    function frame_rng(f: Frame) : set<Addr>


    predicate ws_WF(c: Config, a: ActorAddr, f: Frame, f': Frame)
        requires actor_state_snd(c, a)
    {
        var ws := actor_ws(c, a);
        forall iota ::
            Reachable(c, iota, a, f) ==>
            (iota in actor_ws(c, a) ||
            exists iota' ::
                iota' in ws &&
                subset(frame_rng(f'), ws) &&
                subset(ws, all_reachable(c, a, f')))
    }

    
    predicate all_else_unmodified(c: Config, modified: ActorAddr, c': Config) 
    {
        (forall a ::
            !actor_state_snd(c, modified) &&
            a != modified ==>
            unchanged_actor(c, a, c')) &&

        (forall a ::
            actor_state_snd(c, modified) &&
            a != modified &&
            a != actor_state_snd_a'(c, modified) ==>
            unchanged_actor(c, a, c')) &&

        (actor_state_snd(c, modified) ||
        actor_state_rcv(c, modified) ==>
        forall i :: 
            i !in actor_ws(c, modified) ==>
            unchanged_object(c, i, c'))
    }

    predicate unchanged_object(c: Config, iota: Addr, c': Config)
    {
         OMC(c, iota) == OMC(c', iota) && 
         LRC(c, iota) == LRC(c', iota) &&
         FRC(c, iota) == FRC(c', iota) &&
         AMC(c, iota) == AMC(c', iota)
    }

    predicate unchanged_actor(c: Config, a: ActorAddr, c': Config)
    {
        queue_length(c, a) == queue_length(c', a) &&
        (forall i, n: nat ::
            msg_live(c, a, i, n) <==> 
            msg_live(c', a, i, n)) &&
        
        (forall i ::
            RC(c, i, a) == RC(c', i, a))
    }
    ////////////////////////////////////////////////////// 

    ////////////////////ABSTRACT ADTs/////////////////////

    ///////////SETS///////////
    predicate subset(Set: set<Addr>, subset: set<Addr>) {
        forall iota ::  
            iota in subset ==>
            iota in Set
    }

    predicate disjoint(Set: set<VarId>, Set': set<VarId>) {
        forall iota ::  
            iota in Set ==>
            iota !in Set'
    }
    
    function union(Set: set<Addr>, Set': set<Addr>) : set<Addr>
    ensures forall iota ::
            (iota in Set || 
            iota in Set') ==>
            iota in union(Set, Set')
    /////////////////////////

    /////////QUEUES/////////
    function queue_length(c: Config, a: ActorAddr) : nat

    //nth message in the queue
    function queue_n(c: Config, a: ActorAddr, n: nat) : Msg

    function prev_message(c: Config, a: ActorAddr, n: nat) : Msg
    {
        if n >= 1 then queue_n(c, a, n-1) else Msg.ERR
    }

    predicate WF_queue(c: Config, a: ActorAddr) {
        (forall n: nat :: 
            n < queue_length(c,a) ==> 
            queue_n(c, a, n) != Msg.ERR) &&

        (forall n: nat :: 
            n >= queue_length(c,a) ==> 
            queue_n(c,a,n) == Msg.ERR)
    }

    predicate push(c: Config, a: ActorAddr, msg: Msg, c': Config)
    {
        WF_queue(c, a) &&
        msg != Msg.ERR &&
        queue_length(c', a) == queue_length(c, a) + 1 &&
        queue_n(c', a, queue_length(c,a)) == msg &&

        (forall n: nat :: 
            n != queue_length(c,a) ==>
            queue_n(c', a, n) == queue_n(c, a, n))
    }

    lemma {:verify false} push_preserves_WF_queue(c: Config, a: ActorAddr, msg: Msg, c': Config)
        requires push(c, a, msg, c')
        ensures WF_queue(c', a)
    {
    }

    predicate pop(c:Config, a:ActorAddr, c': Config)
    {
        WF_queue(c, a) &&
        queue_length(c', a) == queue_length(c, a) - 1 &&

        (forall n: nat ::
            n >= 0 ==>
            queue_n(c', a, n) == queue_n(c, a, n+1))
    }

    lemma {:verify false} pop_preserves_WF_queue(c: Config, a: ActorAddr, c': Config)
        requires pop(c, a, c')
        ensures WF_queue(c', a)
    {
    }

    //ORCA MESSAGES IN QUEUE//
    predicate queue_at_n_orca(c: Config, a: ActorAddr, n: nat)
        ensures queue_at_n_orca(c, a, n) ==> n <= queue_length(c, a)
    {
        WF_queue(c, a) &&
        queue_n(c, a, n).orca?
    }

    function queue_at_n_orca_i(c: Config, a: ActorAddr, n: nat) : Addr
        requires queue_at_n_orca(c, a, n)
    {
        queue_n(c, a, n).i
    }

    function queue_at_n_orca_z(c: Config, a: ActorAddr, n: nat) : int
        requires queue_at_n_orca(c, a, n)
    {
        queue_n(c, a, n).z
    }
    
    //APP MESSAGES IN QUEUE//
    predicate queue_at_n_app(c: Config, a: ActorAddr, n: nat)
        ensures queue_at_n_app(c, a, n) ==> n <= queue_length(c, a)
    {
        WF_queue(c, a) &&
        queue_n(c, a, n).app?
    }

    function queue_at_n_app_is(c: Config, a: ActorAddr, n: nat) : set<Addr>
        requires queue_at_n_app(c, a, n)
    {
        queue_n(c, a, n).is
    }
    
    function queue_at_n_app_b(c: Config, a: ActorAddr, n: nat) : BId
        requires queue_at_n_app(c, a, n)
    {
        queue_n(c, a, n).b
    }
    /////////////////////////
    ////////////////////////////////////////////////////// 

}


