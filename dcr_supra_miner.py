# The MIT License (MIT)
#
# Copyright (c) 2014 Richard Moore
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.


# What is this?
#
# NightMiner is meant to be a simple, one-file implementation of a stratum CPU
# miner for CryptoCurrency written in Python favouring understandability
# over performance.
#
# It was originally designed for scrypt-based coins, and has been extended to
# include support for sha256d.
#
# Try running nightminer with the -P and -d to see protocol and debug details
#
# Required reading:
#   Block Hashing Algorithm - https://litecoin.info/Block_hashing_algorithm
#   Stratum Mining Protocol - http://mining.bitcoin.cz/stratum-mining/
#   Scrypt Algorithm        - http://www.tarsnap.com/scrypt/scrypt.pdf
#   Scrypt Implementation   - https://code.google.com/p/scrypt/source/browse/trunk/lib/crypto/crypto_scrypt-ref.c


'''
 -----------------
 Hacked for deCRED 
 -----------------
'stratum+tcp://dcr.suprnova.cc:2255'
'devwarrior.dcr', 
'123'

Blake-256    - hashiing algo
Slightly different RPC response from supranova for:
    Request  - mining.subscribe
    Response - mining.notify        extra level of jason arrays in result:
                      
                      v                                                    v
    {"id":1,"result":[[["mining.notify","deadbeefcafebabe7af5020000000000"]],"82da9ee0",4]

'''

import base64, binascii, json, hashlib, hmac, math, socket, struct, sys, threading, time, urlparse

''' 
devwarrior777
'''
import blake_hash

from pprint import pprint

# DayMiner (ah-ah-ah), fighter of the...
USER_AGENT = "NightMiner"
VERSION = [0, 1]

# Which algorithm for proof-of-work to use
ALGORITHM_BLAKE256    = 'blake256'

ALGORITHMS = [ ALGORITHM_BLAKE256 ]


# Verbosity and log level
QUIET           = False
DEBUG           = False
DEBUG_PROTOCOL  = False

LEVEL_PROTOCOL  = 'protocol'
LEVEL_INFO      = 'info'
LEVEL_DEBUG     = 'debug'
LEVEL_ERROR     = 'error'

def log(message, level):
    '''Conditionally write a message to stdout based on command line options and level.'''
    
    global DEBUG
    global DEBUG_PROTOCOL
    global QUIET
    
    if QUIET and level != LEVEL_ERROR: return
    if not DEBUG_PROTOCOL and level == LEVEL_PROTOCOL: return
    if not DEBUG and level == LEVEL_DEBUG: return
    
    if level != LEVEL_PROTOCOL: message = '[%s] %s' % (level.upper(), message)
    
    print ("[%s] %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), message))

#------------------------------------------------------------------------------
# Utilities
#------------------------------------------------------------------------------

# Convert from/to binary and hexidecimal strings (could be replaced with .encode('hex') and .decode('hex'))
hexlify = binascii.hexlify
unhexlify = binascii.unhexlify


def sha256d(message):
    '''Double SHA256 Hashing function. Currently used on merkle tree hashing <- not sure if that is correct for deCRED tho'''
 
    return hashlib.sha256(hashlib.sha256(message).digest()).digest()


def swap_endian_word(hex_word):
    '''Swaps the endianness of a hexidecimal string of a word and converts to a binary string.'''
  
    message = unhexlify(hex_word)
    if len(message) != 4: raise ValueError('Must be 4-byte word')
    return message[::-1]


def swap_endian_words(hex_words):
    '''Swaps the endianness of a hexidecimal string of words and converts to binary string.'''
  
    message = unhexlify(hex_words)
    if len(message) % 4 != 0: raise ValueError('Must be 4-byte word aligned')
    return ''.join([ message[4 * i: 4 * i + 4][::-1] for i in range(0, len(message) // 4) ])


def human_readable_hashrate(hashrate):
    '''Returns a human readable representation of hashrate.'''
  
    if hashrate < 1000:
        return '%2f hashes/s' % hashrate
    if hashrate < 10000000:
        return '%2f khashes/s' % (hashrate / 1000)
    if hashrate < 10000000000:
        return '%2f Mhashes/s' % (hashrate / 1000000)
    return '%2f Ghashes/s' % (hashrate / 1000000000)



#------------------------------------------------------------------------------
# JOB
#------------------------------------------------------------------------------

class Job(object):
    '''Encapsulates a Job from the network and necessary helper methods to mine.
  
       "If you have a procedure with 10 parameters, you probably missed some."
             ~Alan Perlis
    '''
  
    def __init__(self, job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime, target, extranounce1, extranounce2_size, proof_of_work):
  
        # Job parts from the mining.notify command
        self._job_id = job_id
        self._prevhash = prevhash
        self._coinb1 = coinb1
        self._coinb2 = coinb2
        self._merkle_branches = [ b for b in merkle_branches ]
        self._version = version
        self._nbits = nbits
        self._ntime = ntime
       
        # Job information needed to mine from mining.subsribe
        self._target = target
        self._extranounce1 = extranounce1
        self._extranounce2_size = extranounce2_size
       
        # Proof of work algorithm
        self._proof_of_work = proof_of_work
       
        # Flag to stop this job's mine coroutine
        self._done = False
       
        # Hash metrics (start time, delta time, total hashes)
        self._dt = 0.0
        self._hash_count = 0
  
    # Accessors
    id = property(lambda s: s._job_id)
    prevhash = property(lambda s: s._prevhash)
    coinb1 = property(lambda s: s._coinb1)
    coinb2 = property(lambda s: s._coinb2)
    merkle_branches = property(lambda s: [ b for b in s._merkle_branches ])
    version = property(lambda s: s._version)
    nbits = property(lambda s: s._nbits)
    ntime = property(lambda s: s._ntime)
  
    target = property(lambda s: s._target)
    extranounce1 = property(lambda s: s._extranounce1)
    extranounce2_size = property(lambda s: s._extranounce2_size)
  
    proof_of_work = property(lambda s: s._proof_of_work)
  
  
    @property
    def hashrate(self):
        '''The current hashrate, or if stopped hashrate for the job's lifetime.'''
        
        if self._dt == 0: return 0.0
        return self._hash_count / self._dt
  
  
    def merkle_root_bin(self, extranounce2_bin):
        '''Builds a merkle root from the merkle tree'''
        
        coinbase_bin = unhexlify(self._coinb1) + unhexlify(self._extranounce1) + extranounce2_bin + unhexlify(self._coinb2)
        coinbase_hash_bin = sha256d(coinbase_bin)
        
        merkle_root = coinbase_hash_bin
        for branch in self._merkle_branches:
            merkle_root = sha256d(merkle_root + unhexlify(branch))
        return merkle_root
  
  
    def stop(self):
        '''Requests the mine coroutine stop after its current iteration.'''
  
        self._done = True
  
  
    def mine(self, nounce_start = 0, nounce_stride = 1):
        '''Returns an iterator that iterates over valid proof-of-work shares.
        
           This is a co-routine; that takes a LONG time; the calling thread should look like:
        
             for result in job.mine(self):
               submit_work(result)
        
           nounce_start and nounce_stride are useful for multi-processing if you would like
           to assign each process a different starting nounce (0, 1, 2, ...) and a stride
           equal to the number of processes.
        '''
        dots = 0
        t0 = time.time()
        
        # @TODO: test for extranounce != 0... Do I reverse it or not?
        for extranounce2 in xrange(0, 0x7fffffff):
        
            # Must be unique for any given job id, according to http://mining.bitcoin.cz/stratum-mining/ but never seems enforced?
            extranounce2_bin = struct.pack('<I', extranounce2)
            
            merkle_root_bin = self.merkle_root_bin(extranounce2_bin)
            header_prefix_bin = swap_endian_word(self._version) + swap_endian_words(self._prevhash) + merkle_root_bin + swap_endian_word(self._ntime) + swap_endian_word(self._nbits)
            for nounce in xrange(nounce_start, 0x7fffffff, nounce_stride):
                # This job has been asked to stop
                if self._done:
                    self._dt += (time.time() - t0)
                    raise StopIteration()
                
                # Proof-of-work attempt
                nounce_bin = struct.pack('<I', nounce)
                pofw = self.proof_of_work(header_prefix_bin + nounce_bin)[::-1].encode('hex')

#                 if dots%1000000==0:
#                     sys.stderr.write('.')
#                 dots = dots + 1
                              
                # Did we reach or exceed our target?
                if pofw <= self.target:
                    print(' --- success pow --- : ', pofw)
                    result = dict(
                        job_id = self.id,
                        extranounce2 = hexlify(extranounce2_bin),
                        ntime = str(self._ntime),                    # Convert to str from json unicode
                        nounce = hexlify(nounce_bin[::-1])
                    )
                    self._dt += (time.time() - t0)
                
                    yield result
                
                    t0 = time.time()
                
                self._hash_count += 1
            
        
    def __str__(self):
        return '<Job id=%s prevhash=%s coinb1=%s coinb2=%s merkle_branches=%s version=%s nbits=%s ntime=%s target=%s extranounce1=%s extranounce2_size=%d>' % (self.id, self.prevhash, self.coinb1, self.coinb2, self.merkle_branches, self.version, self.nbits, self.ntime, self.target, self.extranounce1, self.extranounce2_size)


#------------------------------------------------------------------------------
# Subscription
#------------------------------------------------------------------------------

# Subscription state
class Subscription(object):
    '''Encapsulates the Subscription state from the JSON-RPC server'''
    
    # Subclasses should override this
    def ProofOfWork(self, header):
        raise Exception('Do not use the Subscription class directly, subclass it')
    
    class StateException(Exception): pass
    
    def __init__(self):
        self._id = None
        self._difficulty = None
        self._extranounce1 = None
        self._extranounce2_size = None
        self._target = None
        self._worker_name = None
        
        self._mining_thread = None
    
    # Accessors
    id = property(lambda s: s._id)
    worker_name = property(lambda s: s._worker_name)
    
    difficulty = property(lambda s: s._difficulty)
    target = property(lambda s: s._target)
    
    extranounce1 = property(lambda s: s._extranounce1)
    extranounce2_size = property(lambda s: s._extranounce2_size)
    
    
    def set_worker_name(self, worker_name):
        if self._worker_name:
            raise self.StateException('Already authenticated as %r (requesting %r)' % (self._worker_name, worker_name))
    
        self._worker_name = worker_name
    
    
    def _set_target(self, target):
        self._target = '%064x' % target
    
    
    def set_difficulty(self, difficulty):
        if difficulty < 0: raise self.StateException('Difficulty must be non-negative')
        
        # Compute target
        if difficulty == 0:
            target = 2 ** 256 - 1
        else:
            target = min(int((0xffff0000 * 2 ** (256 - 64) + 1) / difficulty - 1 + 0.5), 2 ** 256 - 1)
        
        self._difficulty = difficulty
        self._set_target(target)
        log("New difficulty {0}, target {1}  <-----------------------------".format(difficulty, target), LEVEL_DEBUG)
    
    
    def set_subscription(self, subscription_id, extranounce1, extranounce2_size):
        if self._id is not None:
            raise self.StateException('Already subscribed')
        
        self._id = subscription_id
        self._extranounce1 = extranounce1
        self._extranounce2_size = extranounce2_size
        
    
    def create_job(self, job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime):
        '''Creates a new Job object populated with all the goodness it needs to mine.'''
        
        if self._id is None:
            raise self.StateException('Not subscribed')
        
        return Job(
            job_id = job_id,
            prevhash = prevhash,
            coinb1 = coinb1,
            coinb2 = coinb2,
            merkle_branches = merkle_branches,
            version = version,
            nbits = nbits,
            ntime = ntime,
            target = self.target,
            extranounce1 = self._extranounce1,
            extranounce2_size = self.extranounce2_size,
            proof_of_work = self.ProofOfWork
        )
    
    
    def __str__(self):
        return '<Subscription id=%s, extranounce1=%s, extranounce2_size=%d, difficulty=%d worker_name=%s>' % (self.id, self.extranounce1, self.extranounce2_size, self.difficulty, self.worker_name)


class SubscriptionBlake256(Subscription):
    '''Subscription for Blake-256 for Decred.'''
    
    def ProofOfWork(self, header):
        return blake_hash.getPoWHash(header)

#     def _set_target(self, target):
#         ''' Which does the dcr pool do? '''
#         self._target = '%064x' % target

#     def _set_target(self, target):
#         # Why multiply by 2**16? See: https://litecoin.info/Mining_pool_comparison
#         self._target = '%064x' % (target << 16)

# Maps algorithms to their respective subscription objects, only one for now
SubscriptionByAlgorithm = { ALGORITHM_BLAKE256: SubscriptionBlake256 }



#------------------------------------------------------------------------------
# JSON RPC
#------------------------------------------------------------------------------

class SimpleJsonRpcClient(object):
    '''Simple JSON-RPC client.
    
      To use this class:
        1) Create a sub-class
        2) Override handle_reply(self, request, reply)
        3) Call connect(socket)
    
      Use self.send(method, params) to send JSON-RPC commands to the server.
    
      A new thread is created for listening to the connection; so calls to handle_reply
      are synchronized. It is safe to call send from withing handle_reply.
    '''

    class ClientException(Exception): pass
    
    class RequestReplyException(Exception):
        def __init__(self, message, reply, request = None):
            Exception.__init__(self, message)
            self._reply = reply
            self._request = request
    
        request = property(lambda s: s._request)
        reply = property(lambda s: s._reply)
    
    class RequestReplyWarning(RequestReplyException):
        '''Sub-classes can raise this to inform the user of JSON-RPC server issues.'''
        pass
    
    def __init__(self):
        self._socket = None
        self._lock = threading.RLock()
        self._rpc_thread = None
        self._message_id = 1
        self._requests = dict()
    
    
    def _handle_incoming_rpc(self):
        data = ""
        while True:
            # Get the next line if we have one, otherwise, read and block
            if '\n' in data:
                (line, data) = data.split('\n', 1)
            else:
                chunk = self._socket.recv(1024)
                data += chunk
                continue
            
            log('JSON-RPC Server > ' + line, LEVEL_PROTOCOL)
            
            # Parse the JSON
            try:
                reply = json.loads(line)
            except Exception, e:
                log("JSON-RPC Error: Failed to parse JSON %r (skipping)" % line, LEVEL_ERROR)
                continue
            
            try:
                request = None
                with self._lock:
                    if 'id' in reply and reply['id'] in self._requests:
                        request = self._requests[reply['id']]
                    self.handle_reply(request = request, reply = reply)
            except self.RequestReplyWarning, e:
                output = e.message
                if e.request:
                    output += '\n  ' + str(e.request)
                output += '\n  ' + str(e.reply)
                log(output, LEVEL_ERROR)
            
        
    def handle_reply(self, request, reply):
        # Override this method in sub-classes to handle a message from the server
        raise self.RequestReplyWarning('Override this method')
    
    
    def send(self, method, params):
        '''Sends a message to the JSON-RPC server'''
        
        if not self._socket:
            raise self.ClientException('Not connected')
        
        request = dict(id = self._message_id, method = method, params = params)
        message = json.dumps(request)
        pprint(message,indent=3)
        with self._lock:
            self._requests[self._message_id] = request
            self._message_id += 1
            self._socket.send(message + '\n')
        
        log('JSON-RPC Server < ' + message, LEVEL_PROTOCOL)
        
        return request
    
    
    def connect(self, socket):
        '''Connects to a remove JSON-RPC server'''
        
        if self._rpc_thread:
            raise self.ClientException('Already connected')
        
        self._socket = socket
        
        self._rpc_thread = threading.Thread(target = self._handle_incoming_rpc)
        self._rpc_thread.daemon = True
        self._rpc_thread.start()


#------------------------------------------------------------------------------
# MINER
#------------------------------------------------------------------------------

# Miner client
class Miner(SimpleJsonRpcClient):
    '''Simple mining client'''
    
    class MinerWarning(SimpleJsonRpcClient.RequestReplyWarning):
        def __init__(self, message, reply, request = None):
            SimpleJsonRpcClient.RequestReplyWarning.__init__(self, 'Mining Sate Error: ' + message, reply, request)
    
    class MinerAuthenticationException(SimpleJsonRpcClient.RequestReplyException): pass
    
    def __init__(self, url, username, password, algorithm = ALGORITHM_BLAKE256):
        SimpleJsonRpcClient.__init__(self)
        
        self._url = url
        self._username = username
        self._password = password
        
        self._subscription = SubscriptionByAlgorithm[algorithm]()
        
        self._job = None
        
        self._accepted_shares = 0
    
    # Accessors
    url = property(lambda s: s._url)
    username = property(lambda s: s._username)
    password = property(lambda s: s._password)
    
    
    # Overridden from SimpleJsonRpcClient
    def handle_reply(self, request, reply):
    
        # New work, stop what we were doing before, and start on this.
        if reply.get('method') == 'mining.notify':
            print('mining.notify')
            if 'params' not in reply or len(reply['params']) != 9:
                raise self.MinerWarning('Malformed mining.notify message', reply)
        
            (job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime, clean_jobs) = reply['params']
            self._spawn_job_thread(job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime)
        
            log('New job: job_id={0} version={1} nbits={2} ntime={3}'.format(job_id, version, int(nbits,16), int(ntime,16)), LEVEL_DEBUG)
        
        # The server wants us to change our difficulty (on all *future* work)
        elif reply.get('method') == 'mining.set_difficulty':
            print('mining.set_difficulty')
            if 'params' not in reply or len(reply['params']) != 1:
                raise self.MinerWarning('Malformed mining.set_difficulty message', reply)
        
            (difficulty, ) = reply['params']
            self._subscription.set_difficulty(difficulty)
        
            log('Change difficulty: difficulty=%s' % difficulty, LEVEL_DEBUG)
        
        # This is a reply to...
        elif request:                
        
            # ...subscribe; set-up the work and request authorization
            if request.get('method') == 'mining.subscribe':
                #
                # Changed from above as dcr.supranova.cc pool changed the json structure
                #
                # {"id":1,"result":[[["mining.notify","deadbeefcafebabe68fc020000000000"]],"ad0ac07c",4],"error":null}
                #
                print('mining.subscribe reply')
                if 'result' not in reply or len(reply['result']) != 3 or len(reply['result'][0]) != 1  or len(reply['result'][0][0]) != 2:
                    raise self.MinerWarning('Reply to mining.subscribe is malformed [1]', reply, request)
                
                mining_notify = reply['result'][0][0][0]
                if mining_notify != 'mining.notify':
                    raise self.MinerWarning('Reply to mining.subscribe is malformed [2]', reply, request)
                subscription_id = reply['result'][0][0][1]
                extranounce1 = reply['result'][1]
                extranounce2_size = reply['result'][2] 
                
                self._subscription.set_subscription(subscription_id, extranounce1, extranounce2_size)
                
                log('Subscribed: subscription_id=%s' % subscription_id, LEVEL_DEBUG)
                
                # Request authentication
                self.send(method = 'mining.authorize', params = [ self.username, self.password ])
                
            # ...authorize; if we failed to authorize, quit
            elif request.get('method') == 'mining.authorize':
                print('mining.authorize reply')
                if 'result' not in reply or not reply['result']:
                    raise self.MinerAuthenticationException('Failed to authenticate worker', reply, request)
                
                worker_name = request['params'][0]
                self._subscription.set_worker_name(worker_name)
                
                log('Authorized: worker_name=%s' % worker_name, LEVEL_DEBUG)
                
            # ...submit; complain if the server didn't accept our submission
            elif request.get('method') == 'mining.submit':
                print('mining.submit reply')
                if 'result' not in reply or not reply['result']:
                    log('Share - Invalid', LEVEL_INFO)
                    raise self.MinerWarning('Failed to accept submit', reply, request)
                
                self._accepted_shares += 1
                log('Accepted shares: %d' % self._accepted_shares, LEVEL_INFO)
        
            # ??? *shrug*
            else:
                raise self.MinerWarning('Unhandled message', reply, request)
        
        # ??? *double shrug*
        else:
            raise self.MinerWarning('Bad message state', reply)
    
    
    def _spawn_job_thread(self, job_id, prevhash, coinb1, coinb2, merkle_branches, version, nbits, ntime):
        '''Stops any previous job and begins a new job.'''
        
        # Stop the old job (if any)
        if self._job: self._job.stop()
        
        # Create the new job
        self._job = self._subscription.create_job(
          job_id = job_id,
          prevhash = prevhash,
          coinb1 = coinb1,
          coinb2 = coinb2,
          merkle_branches = merkle_branches,
          version = version,
          nbits = nbits,
          ntime = ntime
        )
    
        def run(job):
            try:
                for result in job.mine():
                    params = [ self._subscription.worker_name ] + [ result[k] for k in ('job_id', 'extranounce2', 'ntime', 'nounce') ]
                    self.send(method = 'mining.submit', params = params)
                    log("Found share: " + str(params), LEVEL_INFO)
                log("Hashrate: %s" % human_readable_hashrate(job.hashrate), LEVEL_INFO)
            except Exception, e:
                log("ERROR: %s" % e, LEVEL_ERROR)
          
        thread = threading.Thread(target = run, args = (self._job, ))
        thread.daemon = True
        thread.start()
    
    
    def serve_forever(self):
        '''Begins the miner. This method does not return.'''
        
        # Figure out the hostname and port
        url = urlparse.urlparse(self.url)
        hostname = url.hostname or ''
        port = url.port or 9333
        
        log('Starting server on %s:%d' % (hostname, port), LEVEL_INFO)
        
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.connect((hostname, port))
        self.connect(sock)
        
        self.send(method = 'mining.subscribe', params = [ "%s/%s" % (USER_AGENT, '.'.join(str(p) for p in VERSION)) ])
        
        # Forever...
        while True:
            time.sleep(10)
    
    
#------------------------------------------------------------------------------
# ALGO UNIT TEST
#------------------------------------------------------------------------------
def testAlgo(diff=0.00005):
    # Create a subscription (and fill it in a bit with what a proper server would give us)
    subs = SubscriptionBlake256()
    subs.set_subscription('my_subs_id', '00000000', 4)
#     subs.set_difficulty(1.0 / (2 ** 16))
    subs.set_difficulty(diff)
    subs.set_worker_name('my_fake_worker')
    
    print('---------------')
    print('START ALGO TEST')
    print('---------------')
    
    # Create a job
    job = subs.create_job('my_job', ('0' * 64), ('0' * 118), ('0' * 110), [ ], '00000002', 'deadbeef', '01234567')
    
    # Search for 5 shares
    share_count = 0
    for valid_share in job.mine():
        print "Found a valid share:", valid_share
        share_count += 1
        if share_count == 5: break
    
    print('---------------')
    print('END ALGO TEST - Hashrate:', job.hashrate)
    print('---------------')


#------------------------------------------------------------------------------
# MAIN
#------------------------------------------------------------------------------
# CLI for cpu mining
if __name__ == '__main__':
    # Set the logging level
    DEBUG = True
    DEBUG_PROTOCOL = True
    
    # Adjust the difficulty of the algo unit test
#     testAlgo(diff=0.00001)
    
    # Heigh-ho, heigh-ho, it's off to work we go...
    url = 'stratum+tcp://dcr.suprnova.cc:2255'
    pooluser = 'devwarrior.dcr'
    poolpass = '123'
    miner = Miner(url, pooluser, poolpass)
    log('NEW DCR SUPRA POOL MINER:   URL: {0}   USER: {1}   PASS: {2}'.format(url, pooluser, poolpass), LEVEL_DEBUG)
    miner.serve_forever()
