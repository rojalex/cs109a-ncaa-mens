import asyncio, aiohttp, async_timeout, json, datetime as dt, itertools, re, copy, pickle, math, scipy
from bs4 import BeautifulSoup, SoupStrainer
from time import strptime
from statistics import mean
from scipy.stats.mstats import gmean


async def dictyieldvalues(dictionary):
    for i in dictionary.values():
        yield i

async def gather_with_concurrency(n, *tasks):
    semaphore = asyncio.Semaphore(n)
    async def sem_task(task):
        async with semaphore:
            return await task
    return await asyncio.gather(*(sem_task(task) for task in tasks))


class Team:
    def __init__(self, teamid, fullname, isd1=False, conference=None):
        self.teamid = teamid
        self.fullname = fullname
        self.isd1 = isd1
        self.conference = conference
        self.games = set()
        self.winslosses = [set(),set()]
    
    def addgame(self, game):
        self.games.add(game)
        if not self.teamid in [game.hometeam.teamid, game.awayteam.teamid]:
            raise ValueError(f'{self.fullname} did not play in game {game.gameid}')
        if game.winner() is self:
            self.winslosses[0].add(game)
        else:
            self.winslosses[1].add(game)
    
    def opponent(self, game):
        if game.hometeam is self:
            return game.awayteam
        elif game.awayteam is self:
            return game.hometeam
        else:
            raise ValueError(f'{self.fullname} did not play in game {game.gameid}!')
    
    def D1winslosses(self):
        return [{win for win in self.winslosses[0] if self.opponent(win).isd1}, {loss for loss in self.winslosses[1] if self.opponent(loss).isd1}]
    
    def record(self):
        return [len(self.winslosses[0]), len(self.winslosses[1])]
    
    def D1record(self):
        D1winslosses = self.D1winslosses()
        return [len(D1winslosses[0]), len(D1winslosses[1])]
    
    def conferencerecord(self):
        D1winslosses = self.D1winslosses()
        return [len([game for game in D1winslosses[0] if self.opponent(game).conference == self.conference]), len([game for game in D1winslosses[1] if self.opponent(game).conference == self.conference])]
    
    def winpct(self):
        wins = self.winslosses[0]
        losses = self.winslosses[1]
        if not wins and not losses:
            return 0.
        else:
            return len(wins)/(len(wins)+len(losses))
    
    def D1winpct(self):
        D1winslosses = self.D1winslosses()
        D1wins = D1winslosses[0]
        D1losses = D1winslosses[1]
        if not D1wins and not D1losses:
            return 0.
        else:
            return len(D1wins)/(len(D1wins)+len(D1losses))
    
    def D1weightedwinpct(self):
        D1winslosses = self.D1winslosses()
        D1wins = D1winslosses[0]
        D1losses = D1winslosses[1]
        D1homewins = []
        D1awaywins = []
        D1homelosses = []
        D1awaylosses = []
        D1neutralwins = []
        D1neutrallosses = []
        for game in D1wins:
            if game.neutralsite:
                D1neutralwins.append(game)
            elif game.hometeam is self:
                D1homewins.append(game)
            elif game.awayteam is self:
                D1awaywins.append(game)
        for game in D1losses:
            if game.neutralsite:
                D1neutrallosses.append(game)
            elif game.hometeam is self:
                D1homelosses.append(game)
            elif game.awayteam is self:
                D1awaylosses.append(game)
        D1homewins = [game for game in D1wins if game.hometeam is self]
        D1roadwins = [game for game in D1wins if game.awayteam is self]
        D1homelosses = [game for game in D1losses if game.hometeam is self]
        weightedwins = 1.4*len(D1awaywins)+len(D1neutralwins)+0.6*len(D1homewins)
        weightedlosses = 1.4*len(D1homelosses)+len(D1neutrallosses)+0.6*len(D1awaylosses)
        if not D1wins and not D1losses:
            return 0.
        else:
            return weightedwins/(weightedwins+weightedlosses)
    
    def D1winpctwithoutopponent(self, opponent):
        D1winslosses = self.D1winslosses()
        D1winswithoutopponent = [win for win in D1winslosses[0] if self.opponent(win) is not opponent]
        D1losseswithoutopponent = [loss for loss in D1winslosses[1] if self.opponent(loss) is not opponent]
        if not D1winswithoutopponent and not D1losseswithoutopponent:
            return 0.
        else:
            return len(D1winswithoutopponent)/(len(D1winswithoutopponent)+len(D1losseswithoutopponent))
    
    def opponents(self):
        return [self.opponent(game) for game in self.games]
    
    def D1opponents(self):
        return [self.opponent(game) for game in self.games if self.opponent(game).isd1]
    
    def OWP(self):
        return mean([opponent.D1winpctwithoutopponent(self) for opponent in self.D1opponents()])
    
    def OOWP(self):
        return mean([opponent.OWP() for opponent in self.D1opponents()])
    
    def RPI(self):
        return 0.25*self.D1winpct()+0.5*self.OWP()+0.25*self.OOWP()
    
    def trueRPI(self):
        return 0.25*self.D1weightedwinpct()+0.5*self.OWP()+0.25*self.OOWP()
    
    def offensiverating(self):
        l = []
        for game in self.games:
            rat = game.offensiveratings()
            if rat:
                l.append(rat[self.teamid])
        return mean(l)
    
    def defensiverating(self):
        l = []
        for game in self.games:
            rat = game.offensiveratings()
            if rat:
                l.append(rat[self.opponent(game).teamid])
        return mean(l)


class Game:
    def __init__(self, gameid, time=None, hometeam=None, homescore=0, awayteam=None, awayscore=0, ots=0, neutralsite=False, boxscore=None):
        self.gameid = gameid
        self.time = time
        self.hometeam = hometeam
        self.homescore = homescore
        self.awayteam = awayteam
        self.awayscore = awayscore
        self.neutralsite = neutralsite
        self.ots = ots
        if boxscore:
            self.boxscore = boxscore
        else:
            self.boxscore = dict()
    
    def winner(self):
        if self.homescore > self.awayscore:
            return self.hometeam
        elif self.awayscore > self.homescore:
            return self.awayteam
    
    def loser(self):
        if self.homescore > self.awayscore:
            return self.awayteam
        elif self.awayscore > self.homescore:
            return self.hometeam
    
    def pointtotal(self):
        return self.homescore+self.awayscore
    
    def pointdifferential(self):
        return abs(self.homescore-self.awayscore)
    
    def possessions(self):
        if self.boxscore:
            hometeaminfo = self.boxscore[self.hometeam.teamid]
            awayteaminfo = self.boxscore[self.awayteam.teamid]
            homefg, homefga = hometeaminfo['fg']
            homefta = hometeaminfo['ft'][1]
            homeorb = hometeaminfo['oreb']
            homedrb = hometeaminfo['dreb']
            hometov = hometeaminfo['to']
            awayfg, awayfga = awayteaminfo['fg']
            awayfta = awayteaminfo['ft'][1]
            awayorb = awayteaminfo['oreb']
            awaydrb = awayteaminfo['dreb']
            awaytov = awayteaminfo['to']
            return totalpossessions(homefga, homefta, homeorb, homedrb, homefg, hometov, awayfga, awayfta, awayorb, awaydrb, awayfg, awaytov)
    
    def offensiveratings(self):
        poss = self.possessions()
        ratings = dict()
        ratings[self.hometeam.teamid] = 100*self.homescore/poss
        ratings[self.awayteam.teamid] = 100*self.awayscore/poss
        return ratings


def totalpossessions(teamfga, teamfta, teamorb, teamdrb, teamfg, teamtov, oppfga, oppfta, opporb, oppdrb, oppfg, opptov):
    return 0.5*((teamfga+0.4*teamfta-1.07*(teamorb/(teamorb+oppdrb))*(teamfga-teamfg)+teamtov)+(oppfga+0.4*oppfta-1.07*(opporb/(opporb+teamdrb))*(oppfga-oppfg)+opptov))

def savedata(teams, games, savefile):
    saveteams = [[team.teamid, team.fullname, team.isd1, team.conference] for team in teams.values()]
    savegames = [[game.gameid, game.time, game.hometeam.teamid, game.homescore, game.awayteam.teamid, game.awayscore, game.ots, game.neutralsite, game.boxscore] for game in games.values()]
    pickle.dump([saveteams, savegames], open(savefile,'wb'))

def recalldata(savefile):
    teamsgames = pickle.load(open(savefile,'rb'))
    recallteams = {team[0] : Team(team[0], team[1], isd1=team[2], conference=team[3]) for team in teamsgames[0]}
    recallgames = {game[0] : Game(game[0], time=game[1], hometeam=recallteams[game[2]], homescore=game[3], awayteam=recallteams[game[4]], awayscore=game[5], ots=game[6], neutralsite=game[7], boxscore=game[8]) for game in teamsgames[1]}
    for game in recallgames.values():
        game.hometeam.addgame(game)
        game.awayteam.addgame(game)
    return recallteams, recallgames


async def getD1teams(session, who='women'):
    teams = dict()
    async with session.get(f'https://www.espn.com/{who}s-college-basketball/teams') as resp:
        html = await resp.text()
        teamsoup = BeautifulSoup(html, 'lxml', parse_only=SoupStrainer(text=lambda string: string.startswith("window['__espnfitt__']")))
    columns = json.loads(teamsoup.text[23:-1])['page']['content']['leagueTeams']['columns']
    for column in columns:
        groups = column['groups']
        for group in groups:
            conference = group['nm']
            teamsjson = group['tms']
            for teamjson in teamsjson:
                teamid = int(teamjson['id'])
                fullname = teamjson['n']
                team = Team(teamid, fullname, isd1=True, conference=conference)
                teams[teamid] = team
    return teams

async def getD1teamschedulejson(teamid, session, who='women'):
    print(f'getting team {teamid}')
    schedulejson = None
    while not schedulejson:
        async with session.get(f'https://www.espn.com/{who}s-college-basketball/team/schedule/_/id/{teamid}/season/2020') as resp:
            try:
                with async_timeout.timeout(10.0):
                    html = await asyncio.wait_for(resp.text(), timeout=10.0)
            except aiohttp.client_exceptions.ClientPayloadError:
                print(f'still waiting for team {teamid}, restarting')
                continue
            try:
                schedulesoup = BeautifulSoup(html, 'lxml', parse_only=SoupStrainer(text=lambda string: string.startswith("window['__espnfitt__']")))
                schedulejson = json.loads(schedulesoup.text[23:-1])['page']['content']['scheduleData']
            except json.decoder.JSONDecodeError:
                print(f'problem with team {teamid}')
                pass
    print(f'done getting team {teamid}')
    return teamid, schedulejson

def processschedulejson(teams, team, schedulejson):
    games = dict()
    gamesjson = list(itertools.chain.from_iterable([schedule['events']['post'] for schedule in schedulejson['teamSchedule']]))
    for gamejson in gamesjson:
        gameid = int(gamejson['time']['link'].split('=')[1])
        datetime = dt.datetime.strptime(gamejson['date']['date'], '%Y-%m-%dT%H:%MZ').replace(tzinfo=dt.timezone.utc)
        neutralsite = gamejson['opponent']['neutralSite']
        game = Game(gameid, time=datetime, neutralsite=neutralsite)
        games[gameid] = game
    return games

def processboxscore(div):
    trs = list(itertools.chain.from_iterable(tbody.find_all('tr') for tbody in div.find_all('tbody')))
    try:
        boxscore = emptybox.copy()
        teamtr = [tr for tr in trs if tr.find('td', text='TEAM')][0]
        for td in teamtr.find_all('td'):
            c = td.get('class')[0]
            if c in boxscore:
                boxscore[c] = datamaps[c](td.text)
        return boxscore
    except ValueError:
        boxscore = emptybox.copy()
        for tr in [tr for tr in trs if not tr.get('class') or 'highlight' not in tr.get('class')]:
            for td in tr.find_all('td'):
                c = td.get('class')[0]
                if c in boxscore:
                    prev = boxscore[c]
                    boxscore[c] = dataadds[c](prev, datamaps[c](td.text))
    return boxscore

async def getgameinfo(gameid, session, who='women'):
    print(f'getting game {gameid}')
    gameinfo = dict()
    while not gameinfo:
        async with session.get(f'https://www.espn.com/{who}s-college-basketball/boxscore?gameId={gameid}') as resp:
            try:
                with async_timeout.timeout(10.0):
                    html = await asyncio.wait_for(resp.text(), timeout=10.0)
            except asyncio.exceptions.TimeoutError:
                print(f'still waiting for game {gameid}, restarting')
                continue
            for i in re.findall('espn.gamepackage.(?:home|away)TeamId = \"\d+\"', html):
                if 'home' in i:
                    gameinfo['hometeamid'] = int(i.split('"')[1])
                if 'away' in i:
                    gameinfo['awayteamid'] = int(i.split('"')[1])
            soup = BeautifulSoup(html, 'lxml')
            teamsdiv = soup.find('div', {'class': 'competitors'})
            try:
                teams = teamsdiv.find_all('div', {'class': 'team'}, recursive=False)
            except:
                print(f'problem with {gameid}, trying again')
                gameinfo = dict()
                continue
            for team in teams:
                nameparts = {span.get('class')[0]: span.text for span in team.find_all('span') if span.get('class')[0] in ['long-name', 'short-name']}
                if 'home' in team.get('class'):
                    gameinfo['hometeamname'] = ' '.join([nameparts['long-name'], nameparts['short-name']])
                if 'away' in team.get('class'):
                    gameinfo['awayteamname'] = ' '.join([nameparts['long-name'], nameparts['short-name']])
            status = teamsdiv.find('span', {'class': 'game-time status-detail'}).text
            if 'OT' in status:
                num = status.split('/')[1].split('OT')[0]
                if not num:
                    gameinfo['ots'] = 1
                else:
                    gameinfo['ots'] = int(num)
            else:
                gameinfo['ots'] = 0
            boxscores = soup.find('div', id='gamepackage-boxscore-module').div.find_all('div', recursive=False)
            for div in boxscores:
                if 'gamepackage-home-wrap' in div.get('class'):
                    try:
                        gameinfo['homebox'] = processboxscore(div)
                    except:
                        print(f'problem with {gameid}')
                        return gameid, None
                if 'gamepackage-away-wrap' in div.get('class'):
                    try:
                        gameinfo['awaybox'] = processboxscore(div)
                    except:
                        print(f'problem with {gameid}')
                        return gameid, None
    print(f'done getting game {gameid}')
    return gameid, gameinfo

datamaps = {'fg': lambda i: [int(n) for n in i.split('-')],
            '3pt': lambda i: [int(n) for n in i.split('-')],
            'ft': lambda i: [int(n) for n in i.split('-')],
            'oreb': int,
            'dreb': int,
            'reb': int,
            'ast': int,
            'stl': int,
            'blk': int,
            'to': int,
            'pf': int,
            'pts': int
           }

dataadds = {'fg': lambda i, j: [i[0]+j[0], i[1]+j[1]],
            '3pt': lambda i, j: [i[0]+j[0], i[1]+j[1]],
            'ft': lambda i, j: [i[0]+j[0], i[1]+j[1]],
            'oreb': lambda i, j: i+j,
            'dreb': lambda i, j: i+j,
            'reb': lambda i, j: i+j,
            'ast': lambda i, j: i+j,
            'stl': lambda i, j: i+j,
            'blk': lambda i, j: i+j,
            'to': lambda i, j: i+j,
            'pf': lambda i, j: i+j,
            'pts': lambda i, j: i+j
           }

emptybox = {'fg': [0, 0],
            '3pt': [0, 0],
            'ft': [0, 0],
            'oreb': 0,
            'dreb': 0,
            'reb': 0,
            'ast': 0,
            'stl': 0,
            'blk': 0,
            'to': 0,
            'pf': 0,
            'pts': 0
           }

async def getD1teamsgames(who='women', savefile=None):
    async with aiohttp.ClientSession() as session:
        teams = await getD1teams(session, who=who)
        schedulejsons = await gather_with_concurrency(16, *[getD1teamschedulejson(team.teamid, session, who=who) async for team in dictyieldvalues(teams)])
    games = dict()
    for teamid, schedulejson in schedulejsons:
        games.update(processschedulejson(teams, teams[teamid], schedulejson))
    async with aiohttp.ClientSession() as session:
        gameinfos = await gather_with_concurrency(16, *[getgameinfo(game.gameid, session, who=who) async for game in dictyieldvalues(games)])
    for gameid, gameinfo in gameinfos:
        if gameinfo:
            game = games[gameid]
            hometeamid = gameinfo['hometeamid']
            hometeam = teams.get(hometeamid)
            if not hometeam:
                hometeam = Team(hometeamid, fullname=gameinfo['hometeamname'])
                teams[hometeamid] = hometeam
            awayteamid = gameinfo['awayteamid']
            awayteam = teams.get(awayteamid)
            if not awayteam:
                awayteam = Team(awayteamid, fullname=gameinfo['awayteamname'])
                teams[awayteamid] = awayteam
            game.hometeam = hometeam
            game.awayteam = awayteam
            homebox = gameinfo['homebox']
            awaybox = gameinfo['awaybox']
            game.homescore = homebox.pop('pts')
            game.awayscore = awaybox.pop('pts')
            game.boxscore = {hometeamid: gameinfo['homebox'], awayteamid: gameinfo['awaybox']}
            hometeam.addgame(game)
            awayteam.addgame(game)
        else:
            del games[gameid]
    for teamid, team in list(teams.items()):
        if not team.games:
            del teams[teamid]
    if savefile:
        savedata(teams, games, savefile)
    return teams, games

#KRACH rankings
def cleanexistingties(teamsin, gamesin):
    teams = {team.teamid: Team(team.teamid, team.fullname, isd1=team.isd1, conference=team.conference) for team in teamsin.values()}
    games = {game.gameid: Game(game.gameid, time=game.time, hometeam=teams[game.hometeam.teamid], homescore=game.homescore, awayteam=teams[game.awayteam.teamid], awayscore=game.awayscore, ots=game.ots, boxscore=game.boxscore, neutralsite=game.neutralsite) for game in gamesin.values() if game.winner()}
    for game in list(games.values()):
        game.hometeam.addgame(game)
        game.awayteam.addgame(game)
    for teamid, team in list(teams.items()):
        if not team.games:
            del teams[teamid]
    return teams, games

def cleannonD1(teamsin, gamesin):
    teams = {team.teamid: Team(team.teamid, team.fullname, isd1=team.isd1, conference=team.conference) for team in teamsin.values() if team.isd1}
    games = {game.gameid: Game(game.gameid, time=game.time, hometeam=teams[game.hometeam.teamid], homescore=game.homescore, awayteam=teams[game.awayteam.teamid], awayscore=game.awayscore, ots=game.ots, boxscore=game.boxscore, neutralsite=game.neutralsite) for game in gamesin.values() if game.winner() and game.winner().isd1 and game.loser().isd1}
    for game in list(games.values()):
        game.hometeam.addgame(game)
        game.awayteam.addgame(game)
    return teams, games

def cleanbeforetime(time, teamsin, gamesin):
    teams = {team.teamid: Team(team.teamid, team.fullname, isd1=team.isd1, conference=team.conference) for team in teamsin.values()}
    games = {game.gameid: Game(game.gameid, time=game.time, hometeam=teams[game.hometeam.teamid], homescore=game.homescore, awayteam=teams[game.awayteam.teamid], awayscore=game.awayscore, ots=game.ots, boxscore=game.boxscore, neutralsite=game.neutralsite) for game in gamesin.values() if game.time and game.time >= time}
    for game in list(games.values()):
        game.hometeam.addgame(game)
        game.awayteam.addgame(game)
    return teams, games

def cleanaftertime(time, teamsin, gamesin):
    teams = {team.teamid: Team(team.teamid, team.fullname, isd1=team.isd1, conference=team.conference) for team in teamsin.values()}
    games = {game.gameid: Game(game.gameid, time=game.time, hometeam=teams[game.hometeam.teamid], homescore=game.homescore, awayteam=teams[game.awayteam.teamid], awayscore=game.awayscore, ots=game.ots, boxscore=game.boxscore, neutralsite=game.neutralsite) for game in gamesin.values() if game.time and game.time < time}
    for game in list(games.values()):
        game.hometeam.addgame(game)
        game.awayteam.addgame(game)
    return teams, games

def numplayed(team1, team2):
    return len(team1.games.intersection(team2.games))

def sos(krachratings, team):
    return gmean([krachratings[team.opponent(game).teamid] for game in team.games if team.opponent(game).isd1])

def oocsos(krachratings, team):
    return gmean([krachratings[team.opponent(game).teamid] for game in team.games if team.opponent(game).isd1 and team.opponent(game).conference != team.conference])

'''def sos(krachratings, team):
    return sum(krachratings[opponent.teamid]*numplayed(team, opponent)/(krachratings[opponent.teamid]+krachratings[team.teamid]) for opponent in team.D1opponents())/sum(numplayed(team, opponent)/(krachratings[opponent.teamid]+krachratings[team.teamid]) for opponent in team.D1opponents())'''

def conferencestrength(krachratings, teams, conference):
    return gmean([krachratings[team.teamid] for team in teams.values() if team.conference == conference])

def victorypoints(team, alpha):
    D1winslosses = team.D1winslosses()
    return sum([1/(1+math.exp(-game.pointdifferential()/(alpha*game.pointtotal()))) for game in D1winslosses[0]]+[1/(1+math.exp(game.pointdifferential()/(alpha*game.pointtotal()))) for game in D1winslosses[1]])

def rrwp(krachratings, team):
    teamrating = krachratings[team.teamid]
    return sum([teamrating/(teamrating+krachratings[opponentid]) for opponentid in krachratings if opponentid != team.teamid])/(len(krachratings)-1)

def rrwpkrach(krachratings, rating):
    return sum([rating/(rating+opprating) for opprating in krachratings.values()])/len(krachratings)

def krachadj(krachratings):
    return scipy.optimize.fsolve(lambda rating: rrwpkrach(krachratings, rating)-0.5, 100)[0]

def calckrachratings(teamsin, gamesin, vpalpha=5, goaldelta=1e-10, time=None, sincetime=None, savefile=None, calcteamsos=True, printstat=False):
    teams, games = cleanexistingties(teamsin, gamesin)
    if time:
        teams, games = cleanaftertime(time, teams, games)
    if sincetime:
        teams, games = cleanbeforetime(sincetime, teams, games)
    D1teams = {team.teamid: team for team in teams.values() if team.isd1}
    
    krachratings = {teamid: 100. for teamid, team in D1teams.items() if team.isd1}
    
    iterations = 0
    alphaadj = vpalpha/mean([game.pointtotal() for game in games.values() if game.hometeam.isd1 and game.awayteam.isd1])
    victorypoints_dict = dict()
    D1opponents_dict = dict()
    numplayed_dict = dict()
    for team in D1teams.values():
            victorypoints_dict[team] = victorypoints(team, alphaadj)
            D1opponents = set(team.D1opponents())
            D1opponents_dict[team] = D1opponents
            for opponent in D1opponents:
                numplayed_dict[frozenset({team, opponent})] = numplayed(team, opponent)
    while True:
        if printstat:
            print(f'Iteration {iterations+1}')
        newkrachratings = dict(krachratings)
        delta = 0.
        
        for team in D1teams.values():
            newkrachratings[team.teamid] = victorypoints_dict[team]/sum(numplayed_dict[frozenset({team, opponent})]/(krachratings[team.teamid]+krachratings[opponent.teamid]) for opponent in D1opponents_dict[team])
            delta += abs(newkrachratings[team.teamid]-krachratings[team.teamid])
        
        krachratings = dict(newkrachratings)
        
        if printstat:
            print(delta)
        if delta < goaldelta*gmean(list(krachratings.values())):
            adj = krachadj(krachratings)
            krachratings = {k: v*100/adj for k, v in krachratings.items()}
            break
        
        iterations += 1
    if calcteamsos:
        teamsos = {team.teamid: sos(krachratings, team) for team in D1teams.values()}
    if savefile:
        if calcteamsos:
            pickle.dump([krachratings, teamsos], open(savefile,'wb'))
        else:
            pickle.dump(krachratings, open(savefile,'wb'))
    if calcteamsos:
        return krachratings, teamsos
    else:
        return krachratings
