FROM ubuntu:latest
ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
	&& apt-get -y install --no-install-recommends python3 ipython3 python3-tk git unzip vim curl gnupg nodejs npm xz-utils \
												libx11-xcb1 libxtst6 libsecret-1-0 

# https://github.com/puppeteer/puppeteer/blob/main/docs/troubleshooting.md#chrome-headless-doesnt-launch-on-unix
RUN apt-get install -y wget gnupg \
    && wget -q -O - https://dl-ssl.google.com/linux/linux_signing_key.pub | apt-key add - \
    && sh -c 'echo "deb [arch=amd64] http://dl.google.com/linux/chrome/deb/ stable main" >> /etc/apt/sources.list.d/google.list' \
    && apt-get update \
    && apt-get install -y google-chrome-stable fonts-ipafont-gothic fonts-wqy-zenhei fonts-thai-tlwg fonts-kacst fonts-freefont-ttf libxss1 \
      --no-install-recommends \
     && rm -rf /var/lib/apt/lists/*

RUN apt update
RUN apt -y install python3-pip
RUN pip3 install numpy pandas scipy matplotlib

RUN npm install --global yarn
RUN npm install --global node-abi
RUN npm install --global typescript mocha jest nyc

RUN mkdir -p /home/resynchronizer

COPY . /home/resynchronizer

WORKDIR /home/resynchronizer

RUN git config --global http.sslVerify "false"
RUN npm config set strict-ssl false
RUN ./build.sh
