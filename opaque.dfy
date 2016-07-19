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
    function Heap(i: Addr, fid: FId) : Addr 
    

    ////ADDRESSES////
    datatype Addr = OA(ObjectAddr) | AA(ActorAddr) | Null
    type ObjectAddr
    type ActorAddr
    

    ////ACTORS////
    datatype Actor = Actor(q: Queue, st: State)
    //lemma RANGE OF ACTORS IS FINITE
    //lemma all valid actor addresses are in the domain of Actors
    function Actors(a: ActorAddr, c: Config) : Actor

    //Queues//
    //length added to convince Dafny that queues are finite 
    //Is there a better way?
    datatype Queue = Queue(msg: Msg, length: int) //opaque - how?
    //??
    predicate WF_queue(c: Config, a: ActorAddr) {
        exists n:nat :: NthMsg(c, a, n) != Msg.ERR && n >= 1 ==> NthMsg(c, a, n-1) != Msg.ERR 
                                                                && n <= queue_length(c, a)
    }


    function prev_message(c: Config, a: ActorAddr, n: nat) : Msg
    {
        if n >= 1 then NthMsg(c, a, n-1) else Msg.ERR
    }

    predicate WF_queue'(c: Config, a: ActorAddr) {
        forall n:nat :: NthMsg(c, a, n) == Msg.ERR ==> NthMsg(c,a,n+1) == Msg.ERR
    }


    //States// 
    datatype State = idl | exe(f: Frame) | snd(f': Frame, a: Actor, m: Msg, ws: Workset)
                | mkU(ms: Marks) | trc(ms': Marks) | mkR(ms'': Marks) | cll(ms''': Marks)
    type Marks 
    type Workset = set<Addr> //opaque - how?
    datatype RU = R | U
    function Marks_to_RU(m: Marks) : RU


    ////MESSAGES////
    datatype Msg = orca(i: Addr, z: int) | app(f: Frame) | ERR 
    //datatype Frame = CFrame(b: BId, Map: map<VarId, Addr>) //opaque - how? 
    datatype Frame = Frame(b: BId) 
    function var_to_addr(f: Frame, v: VarId) : Addr
    
    
    ////IDs////
    type FId 
    type BId  
    type ClassId
    type VarId

   
    ////PATHS//// 
    datatype DP = This | LP(zero: int, x: VarId) | MP(k: int, x': VarId) | cons(dp: DP, f: FId)
    datatype SP = This | bsp(b: BId, x: VarId) | cons(sp: SP, f: FId)
    datatype Capability = WRITE | READ | TAG | ERR


    ////REFERENCE COUNTS////
    function RC(c: Config, i: Addr, a: ActorAddr) : int 
    function OMC(c: Config, i: Addr) : int
    function LRC(c: Config, i: Addr) : int
    function FRC(c: Config, i: Addr) : int
    function AMC(c: Config, i: Addr) : int 
    //{|(set x | exists a,k :: 0<=k<queue_length(c, a) && x==(a,k) && Reach(c,a,k,i))|}
    
    function Owner(c: Config, i: Addr) : ActorAddr
    function Field(c: Config, i: Addr, f: FId) : Addr //what do we need this for?
    function Class(c: Config, a: ActorAddr) : ClassId 
    function NthMsg(c: Config, a: ActorAddr, n: nat) : Msg 
    function Addrs(c: Config) : set<ActorAddr>
    
    predicate Reach(c: Config, a: ActorAddr, n: nat, i: Addr)

    
    ////AUXILIARY FUNCTION////
    //TODO: separate into its own module
    function queue_length(c: Config, a: ActorAddr) : int {
        Actors(a,c).q.length
    }
    
}
